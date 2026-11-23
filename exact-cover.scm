;;;; exact-cover.scm - exact cover problems by a purely functional Algorithm X
;;;
;;; Solves exact cover problems: given items 0 .. n-1 and a list of
;;; options (sets of items), find every choice of options that covers
;;; each primary item exactly once and each secondary item at most once.
;;; Sudoku and the n queens problem are common examples.
;;;
;;; The search is based on Knuth's Algorithm X.  It picks the
;;; uncovered primary item with the fewest remaining options, branches
;;; on each of those options, and in each branch drops the options
;;; that clash with the one chosen.
;;;
;;; The design follows Henning Thielemann's Haskell set-cover library,
;;; where search states are immutable values rather than dancing-links
;;; structures.  Backtracking does not need undo, a state can be searched
;;; more than once, and fixed choices (such as puzzle givens) are made
;;; by choosing options before the search starts.  Sets of items and
;;; options are bit sets, and each option keeps the precomputed set of
;;; options it clashes with, so choosing an option costs one set
;;; difference.
;;;
;;; The search counts nodes visited, guesses (nodes with two or more
;;; candidate options) and updates (options removed), as a measure of
;;; how hard a problem was.

(module exact-cover
  (
   ;; Problems and search states
   make-exact-cover exact-cover-state?
   exact-cover-item-count exact-cover-option-count
   exact-cover-chosen exact-cover-uncovered exact-cover-available
   exact-cover-complete?
   exact-cover-choose exact-cover-choose*
   exact-cover-branch exact-cover-step

   ;; Search
   exact-cover-fold exact-cover-solutions exact-cover-count
   search-stats search-stats? search-stats-nodes search-stats-guesses
   search-stats-updates search-stats->alist
   )

  (import
   scheme
   (only (scheme base) vector-map vector-for-each vector-copy)
   (chicken base)
   (chicken fixnum)
   (srfi 1)
   (srfi 69)
   datatype
   )

  ;;; ==================================================================
  ;;; Bit sets
  ;;; ==================================================================

  ;; A bit set over 0 .. n-1 is a vector of fixnum words, word w holding
  ;; the members w B .. w B + B - 1 where B is word-bits.  Only the
  ;; constructors below write to a vector; every set handed out is
  ;; treated as a value.

  (define word-bits (fx- fixnum-bits 1))

  (define (bitset-words n) (fxmax 1 (fx/ (fx+ n (fx- word-bits 1)) word-bits)))

  (define (list->bitset n members)
    (let ((v (make-vector (bitset-words n) 0)))
      (for-each (lambda (i)
                  (let ((w (fx/ i word-bits)))
                    (vector-set! v w (fxior (vector-ref v w) (fxshl 1 (fxmod i word-bits))))))
                members)
      v))

  (define (bitset-member? s i)
    (not (fx= 0 (fxand (vector-ref s (fx/ i word-bits)) (fxshl 1 (fxmod i word-bits))))))

  (define (bitset-empty? s)
    (let loop ((w 0))
      (or (fx= w (vector-length s))
          (and (fx= 0 (vector-ref s w)) (loop (fx+ w 1))))))

  (define (bitset-and a b)
    (let* ((n (vector-length a))
           (out (make-vector n 0)))
      (do ((w 0 (fx+ w 1))) ((fx= w n) out)
        (vector-set! out w (fxand (vector-ref a w) (vector-ref b w))))))

  (define (bitset-difference a b)
    (let* ((n (vector-length a))
           (out (make-vector n 0)))
      (do ((w 0 (fx+ w 1))) ((fx= w n) out)
        (vector-set! out w (fxand (vector-ref a w) (fxnot (vector-ref b w)))))))

  (define (bitset-fold f acc s)
    ;; Folds F over the members of S in increasing order: (F i acc).
    (let word-loop ((w 0) (acc acc))
      (if (fx= w (vector-length s))
          acc
          (let bit-loop ((x (vector-ref s w)) (acc acc))
            (if (fx= x 0)
                (word-loop (fx+ w 1) acc)
                (let ((low (fxand x (fxneg x))))
                  (bit-loop (fxxor x low)
                            (f (fx+ (fx* w word-bits) (fx- (fxlen low) 1)) acc))))))))

  (define (bitset->list s)
    (reverse (bitset-fold cons '() s)))

  ;;; ==================================================================
  ;;; Problems and search states
  ;;; ==================================================================

  (define (any? x) #t)

  ;; The check of a field holding a list; list? would walk the list.
  (define (list-head? x) (or (null? x) (pair? x)))

  ;; What all states of one problem share.  For option o: its label, its
  ;; items (a vector), its item set and the set of options sharing an
  ;; item with it (o included).  For item i: the options containing it,
  ;; in increasing order (a vector).  branch is the set of items preferred
  ;; for branching, or #f; table maps labels to option indices.
  (define-datatype cover-problem cover-problem?
    (CoverProblem (n-items fixnum?)
                  (labels vector?)
                  (option-items vector?)
                  (option-sets vector?)
                  (conflicts vector?)
                  (item-options vector?)
                  (branch any?)
                  (table hash-table?)))

  (define (problem-n-items p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) n)))
  (define (problem-labels p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) l)))
  (define (problem-option-items p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) oi)))
  (define (problem-option-sets p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) os)))
  (define (problem-conflicts p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) c)))
  (define (problem-item-options p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) io)))
  (define (problem-branch p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) b)))
  (define (problem-table p)
    (cases cover-problem p (CoverProblem (n l oi os c io b t) t)))

  ;; A search state: the set of available options (those disjoint from
  ;; every chosen option) and how many there are, the number of available
  ;; options containing each item (a vector), the set of uncovered
  ;; primary items, and the labels of the chosen options, the most recent
  ;; first.
  ;; States are made only inside this module, so the problem field is
  ;; not checked on every construction.
  (define-datatype exact-cover-state exact-cover-state?
    (CoverState (problem any?)
                (available vector?)
                (n-available fixnum?)
                (counts vector?)
                (uncovered vector?)
                (chosen list-head?)))

  (define (state-problem st)
    (cases exact-cover-state st (CoverState (p a n k u ch) p)))
  (define (state-available st)
    (cases exact-cover-state st (CoverState (p a n k u ch) a)))
  (define (state-n-available st)
    (cases exact-cover-state st (CoverState (p a n k u ch) n)))
  (define (state-counts st)
    (cases exact-cover-state st (CoverState (p a n k u ch) k)))
  (define (state-uncovered st)
    (cases exact-cover-state st (CoverState (p a n k u ch) u)))
  (define (state-chosen st)
    (cases exact-cover-state st (CoverState (p a n k u ch) ch)))

  (define (exact-cover-item-count st)
    "The number of items of the problem of ST (primary and secondary)."
    (problem-n-items (state-problem st)))

  (define (exact-cover-option-count st)
    "The number of options still available in the state ST."
    (state-n-available st))

  (define (exact-cover-chosen st)
    "The labels of the options chosen in the state ST, in the order they
     were chosen."
    (reverse (state-chosen st)))

  (define (exact-cover-uncovered st)
    "The primary items not yet covered in the state ST, in increasing order."
    (bitset->list (state-uncovered st)))

  (define (exact-cover-available st)
    "The labels of the options that can still be chosen in the state ST,
     in their original order."
    (let ((labels (problem-labels (state-problem st))))
      (map (lambda (o) (vector-ref labels o)) (bitset->list (state-available st)))))

  (define (exact-cover-complete? st)
    "True when every primary item is covered in the state ST, so that its
     chosen options form a solution."
    (bitset-empty? (state-uncovered st)))

  (define (check-item who i)
    (unless (and (fixnum? i) (fx>= i 0))
      (error who "items must be non-negative integers" i)))

  (define (make-exact-cover options #!key (primary #f) (branch-items #f))
    "The initial search state of an exact cover problem.  OPTIONS is a
     list of options, each a list (LABEL ITEM ...) of a label (any value,
     distinct under equal?) and one or more items, non-negative integers.

     Items below PRIMARY must be covered exactly once; items from PRIMARY
     on are secondary and may be covered at most once.  By default every
     item is primary.

     BRANCH-ITEMS, when given, is a list of primary items to branch on in
     preference to the others: the search picks the item with the fewest
     options among the uncovered items of BRANCH-ITEMS, and among all
     uncovered primary items only when none of those is left."
    (let* ((parsed
            (list->vector
             (map (lambda (option)
                    (unless (and (list? option) (pair? option) (pair? (cdr option)))
                      (error 'make-exact-cover "an option is a label and one or more items"
                             option))
                    (let ((items (cdr option)))
                      (for-each (lambda (i) (check-item 'make-exact-cover i)) items)
                      (cons (car option) (list->vector (delete-duplicates items =)))))
                  options)))
           (n-options (vector-length parsed))
           (top (fold (lambda (p m) (fold max m (vector->list (cdr p)))) -1
                      (vector->list parsed)))
           (primary (or primary (+ top 1))))
      (unless (and (fixnum? primary) (fx>= primary 0))
        (error 'make-exact-cover "the number of primary items must be a non-negative integer"
               primary))
      (when branch-items
        (for-each (lambda (i)
                    (check-item 'make-exact-cover i)
                    (unless (< i primary)
                      (error 'make-exact-cover "branch items must be primary items" i)))
                  branch-items))
      (let* ((n-items (max (+ top 1) primary))
             (labels (vector-map car parsed))
             (option-items (vector-map cdr parsed))
             (members (make-vector n-items '()))
             (table (make-hash-table equal?)))
        (do ((o (- n-options 1) (- o 1))) ((< o 0))
          (vector-for-each (lambda (i) (vector-set! members i (cons o (vector-ref members i))))
                           (vector-ref option-items o)))
        (do ((o 0 (+ o 1))) ((= o n-options))
          (let ((label (vector-ref labels o)))
            (when (hash-table-exists? table label)
              (error 'make-exact-cover "two options with the same label" label))
            (hash-table-set! table label o)))
        (let ((item-options (vector-map list->vector members)))
          (CoverState
           (CoverProblem n-items labels option-items
                         (vector-map (lambda (items) (list->bitset n-items (vector->list items)))
                                     option-items)
                         (vector-map (lambda (items)
                                       (list->bitset
                                        n-options
                                        (append-map (lambda (i) (vector->list
                                                                 (vector-ref item-options i)))
                                                    (vector->list items))))
                                     option-items)
                         item-options
                         (and branch-items (list->bitset n-items branch-items))
                         table)
           (list->bitset n-options (iota n-options))
           n-options
           (vector-map vector-length item-options)
           (list->bitset n-items (iota primary))
           '())))))

  (define (apply-option st o)
    ;; The state after choosing the available option O, and the number of
    ;; options it removes.  Each record is taken apart once: the search
    ;; calls this for every state it visits.
    (cases exact-cover-state st
      (CoverState (p available n-available counts uncovered chosen)
        (cases cover-problem p
          (CoverProblem (n-items labels option-items option-sets conflicts
                                 item-options branch table)
            (let* ((conflicts (vector-ref conflicts o))
                   (counts (subvector counts 0))
                   (removed
                    (bitset-fold (lambda (r n)
                                   (let ((items (vector-ref option-items r)))
                                     (do ((j 0 (fx+ j 1))) ((fx= j (vector-length items)))
                                       (let ((i (vector-ref items j)))
                                         (vector-set! counts i (fx- (vector-ref counts i) 1)))))
                                   (fx+ n 1))
                                 0
                                 (bitset-and available conflicts))))
              (values
               (CoverState p
                           (bitset-difference available conflicts)
                           (fx- n-available removed)
                           counts
                           (bitset-difference uncovered (vector-ref option-sets o))
                           (cons (vector-ref labels o) chosen))
               removed)))))))

  (define (exact-cover-choose st label)
    "The state after choosing, in the state ST, the option labelled LABEL,
     or #f when that option shares an item with an option already chosen.
     ST itself is unchanged."
    (let ((o (hash-table-ref/default (problem-table (state-problem st)) label #f)))
      (unless o
        (error 'exact-cover-choose "no option with this label" label))
      (and (bitset-member? (state-available st) o)
           (let-values (((child removed) (apply-option st o)))
             child))))

  (define (exact-cover-choose* st labels)
    "The state after choosing the options labelled LABELS in turn, or #f
     when one of them cannot be chosen."
    (fold (lambda (label st) (and st (exact-cover-choose st label))) st labels))

  (define (select-item st)
    ;; The item to branch on, or #f when the state is complete: the first
    ;; item, in increasing order, with the fewest available options among
    ;; the uncovered branch items, or among all uncovered primary items
    ;; when no branch item is left.  An item with no options ends the scan.
    (cases exact-cover-state st
      (CoverState (p available n-available counts uncovered chosen)
        (let ((candidates (let ((branch (problem-branch p)))
                            (if branch
                                (let ((c (bitset-and uncovered branch)))
                                  (if (bitset-empty? c) uncovered c))
                                uncovered))))
          (let word-loop ((w 0) (best #f) (best-n 0))
            (if (fx= w (vector-length candidates))
                best
                (let bit-loop ((x (vector-ref candidates w)) (best best) (best-n best-n))
                  (if (fx= x 0)
                      (word-loop (fx+ w 1) best best-n)
                      (let* ((low (fxand x (fxneg x)))
                             (i (fx+ (fx* w word-bits) (fx- (fxlen low) 1)))
                             (n (vector-ref counts i)))
                        (cond ((fx= n 0) i)
                              ((or (not best) (fx< n best-n)) (bit-loop (fxxor x low) i n))
                              (else (bit-loop (fxxor x low) best best-n))))))))))))

  (define (branch-options st item)
    ;; The available options containing ITEM, in increasing order.
    (cases exact-cover-state st
      (CoverState (p available n-available counts uncovered chosen)
        (let ((opts (vector-ref (problem-item-options p) item)))
          (let loop ((j (fx- (vector-length opts) 1)) (acc '()))
            (if (fx< j 0)
                acc
                (let ((o (vector-ref opts j)))
                  (loop (fx- j 1) (if (bitset-member? available o) (cons o acc) acc)))))))))

  (define (exact-cover-branch st)
    "The branching step of the state ST, as two values: the uncovered
     primary item contained in the fewest available options (the first
     such item in increasing order, among the branch items when some are
     left), and the labels of the options containing it.  The item is #f
     when ST is complete; the list is empty when ST is a dead end."
    (let ((item (select-item st))
          (labels (problem-labels (state-problem st))))
      (values item
              (if item
                  (map (lambda (o) (vector-ref labels o)) (branch-options st item))
                  '()))))

  (define (exact-cover-step st)
    "The states that follow ST in the search: one for each option
     containing the branching item (see exact-cover-branch).  The list is
     empty when ST is complete or a dead end."
    (let ((item (select-item st)))
      (if item
          (map (lambda (o) (let-values (((child removed) (apply-option st o))) child))
               (branch-options st item))
          '())))

  ;;; ==================================================================
  ;;; Search
  ;;; ==================================================================

  ;; The counts of one search: states visited, states entered through a
  ;; choice among two or more options, and options removed from the
  ;; available sets by the choices made.
  (define-datatype search-stats search-stats?
    (SearchStats (nodes fixnum?) (guesses fixnum?) (updates fixnum?)))

  (define (search-stats-nodes s) (cases search-stats s (SearchStats (n g u) n)))
  (define (search-stats-guesses s) (cases search-stats s (SearchStats (n g u) g)))
  (define (search-stats-updates s) (cases search-stats s (SearchStats (n g u) u)))

  (define (search-stats->alist s)
    "The counts of S as an association list with the keys nodes,
     guesses and updates."
    `((nodes . ,(search-stats-nodes s))
      (guesses . ,(search-stats-guesses s))
      (updates . ,(search-stats-updates s))))

  (define (exact-cover-fold st kons knil #!key (limit #f) (shuffle #f))
    "Searches for the solutions reachable from the state ST and folds
     KONS over them: (KONS labels acc), starting from KNIL, where labels
     are the labels of a solution's options in the order chosen
     (including those chosen before the search).  The search stops after
     LIMIT solutions (#f: all).  SHUFFLE, when given, is a procedure that
     reorders a list; the options of every branch are tried in the order
     it returns, for example a random one.  Returns two values: the
     result of the fold and the search statistics."
    (when (and limit (not (and (fixnum? limit) (fx> limit 0))))
      (error 'exact-cover-fold "the limit must be a positive integer or #f" limit))
    ;; search visits the state ST and the states below it.  It receives
    ;; the counts so far (nodes, guesses, updates, solutions found) and
    ;; the fold result so far, and returns them as five values after the
    ;; visit.  next does the same for the remaining options OS of a
    ;; branch, passing the result of each child's search to the next.
    (define (search st nodes guesses updates found acc)
      (let ((nodes (fx+ nodes 1)))
        (if (exact-cover-complete? st)
            (values nodes guesses updates (fx+ found 1)
                    (kons (reverse (state-chosen st)) acc))
            (let* ((item (select-item st))
                   (opts (if item (branch-options st item) '()))
                   (guess? (and (pair? opts) (pair? (cdr opts))))
                   (opts (if (and shuffle guess?) (shuffle opts) opts)))
              (let next ((os opts) (nodes nodes) (guesses guesses) (updates updates)
                         (found found) (acc acc))
                (if (and (pair? os) (or (not limit) (fx< found limit)))
                    (let-values (((child removed) (apply-option st (car os))))
                      (let-values (((nodes guesses updates found acc)
                                    (search child
                                            nodes
                                            (if guess? (fx+ guesses 1) guesses)
                                            (fx+ updates removed)
                                            found
                                            acc)))
                        (next (cdr os) nodes guesses updates found acc)))
                    (values nodes guesses updates found acc)))))))
    (let-values (((nodes guesses updates found acc) (search st 0 0 0 0 knil)))
      (values acc (SearchStats nodes guesses updates))))

  (define (exact-cover-solutions st #!key (limit #f) (shuffle #f))
    "The solutions reachable from the state ST, at most LIMIT of them, in
     the order found, each a list of option labels; and as a second value
     the search statistics."
    (let-values (((acc stats) (exact-cover-fold st cons '() limit: limit shuffle: shuffle)))
      (values (reverse acc) stats)))

  (define (exact-cover-count st #!key (limit #f))
    "The number of solutions reachable from the state ST, counting no
     further than LIMIT; and as a second value the search statistics."
    (exact-cover-fold st (lambda (labels n) (+ n 1)) 0 limit: limit))

  )
