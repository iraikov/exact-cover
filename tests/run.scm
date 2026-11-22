;;;; run.scm - tests for the exact-cover egg
;;;;
;;;; Problem construction, choosing options, the branching step, the
;;;; search on Knuth's example with its exact counts, items and options
;;;; spanning several bit-set words, solution counts of n queens (with
;;;; secondary items) and domino tilings, limits, branch items and
;;;; shuffled search.

(import scheme
        (chicken base)
        (chicken condition)
        (chicken port)
        (chicken sort)
        (srfi 1)
        test
        exact-cover)

;;; ==================================================================
;;; Test Utilities
;;; ==================================================================

(define (raises? thunk)
  (condition-case (begin (thunk) #f)
    ((exn) #t)))

(define (count-of st #!key (limit #f))
  (let-values (((n stats) (exact-cover-count st limit: limit))) n))

(define (solutions-of st #!key (limit #f) (shuffle #f))
  (let-values (((sols stats) (exact-cover-solutions st limit: limit shuffle: shuffle))) sols))

(define (branch-of st)
  (let-values (((item option-labels) (exact-cover-branch st)))
    (list item option-labels)))

(define (stats-of st)
  (let-values (((sols stats) (exact-cover-solutions st))) (search-stats->alist stats)))

;; Knuth's example from "Dancing Links": items A .. G are 0 .. 6.
(define knuth-options
  '((1 2 4 5)       ; C E F
    (2 0 3 6)       ; A D G
    (3 1 2 5)       ; B C F
    (4 0 3)         ; A D
    (5 1 6)         ; B G
    (6 3 4 6)))     ; D E G

;; The n queens problem: rows 0 .. n-1 and columns n .. 2n-1 are
;; primary, the 2n-1 diagonals and 2n-1 anti-diagonals secondary.
(define (queens n)
  (make-exact-cover
   (append-map (lambda (r)
                 (map (lambda (c)
                        (list (cons r c) r (+ n c) (+ n n r c) (+ n n n n -1 r (- c) n -1)))
                      (iota n)))
               (iota n))
   primary: (* 2 n)))

;; Domino tilings of a rows x cols board: items are the cells, options the
;; horizontal and vertical dominoes.
(define (dominoes rows cols)
  (let ((cell (lambda (r c) (+ (* r cols) c))))
    (make-exact-cover
     (append
      (append-map (lambda (r)
                    (map (lambda (c) (list (list 'h r c) (cell r c) (cell r (+ c 1))))
                         (iota (- cols 1))))
                  (iota rows))
      (append-map (lambda (r)
                    (map (lambda (c) (list (list 'v r c) (cell r c) (cell (+ r 1) c)))
                         (iota cols)))
                  (iota (- rows 1)))))))

(define (sorted-solutions sols)
  ;; Solutions as sorted lists of printed labels, sorted, for comparing
  ;; solution sets found in different orders.
  (let ((key (lambda (labels)
               (sort (map (lambda (l) (with-output-to-string (lambda () (write l)))) labels)
                     string<?))))
    (sort (map key sols)
          (lambda (a b) (string<? (apply string-append a) (apply string-append b))))))

;;; ==================================================================
;;; Problems and states
;;; ==================================================================

(test-group "Problem construction"
  (let ((st (make-exact-cover knuth-options)))
    (test "items" 7 (exact-cover-item-count st))
    (test "all items uncovered" '(0 1 2 3 4 5 6) (exact-cover-uncovered st))
    (test "all options available" '(1 2 3 4 5 6) (exact-cover-available st))
    (test "option count" 6 (exact-cover-option-count st))
    (test "nothing chosen" '() (exact-cover-chosen st))
    (test-assert "not complete" (not (exact-cover-complete? st))))
  (test "secondary items are not to be covered" '(0 1)
        (exact-cover-uncovered (make-exact-cover '((a 0 2) (b 1 3)) primary: 2)))
  (test "primary items beyond the options" '(0 1 2)
        (exact-cover-uncovered (make-exact-cover '((a 0)) primary: 3)))
  (test-assert "an option without items"
               (raises? (lambda () (make-exact-cover '((a))))))
  (test-assert "two options with one label"
               (raises? (lambda () (make-exact-cover '((a 0) (a 1))))))
  (test-assert "a negative item"
               (raises? (lambda () (make-exact-cover '((a -1))))))
  (test-assert "branch items must be primary"
               (raises? (lambda () (make-exact-cover '((a 0 1)) primary: 1 branch-items: '(1))))))

(test-group "Choosing options"
  (let* ((st (make-exact-cover knuth-options))
         (st4 (exact-cover-choose st 4)))
    (test "chosen" '(4) (exact-cover-chosen st4))
    (test "covered items removed" '(1 2 4 5 6) (exact-cover-uncovered st4))
    (test "conflicting options removed" '(1 3 5) (exact-cover-available st4))
    (test-assert "a conflicting option cannot be chosen" (not (exact-cover-choose st4 2)))
    (test "the earlier state is unchanged" '(1 2 3 4 5 6) (exact-cover-available st))
    (test "several choices" '(4 1 5) (exact-cover-chosen (exact-cover-choose* st '(4 1 5))))
    (test-assert "several choices, complete" (exact-cover-complete? (exact-cover-choose* st '(4 1 5))))
    (test-assert "several choices with a conflict" (not (exact-cover-choose* st '(4 2))))
    (test-assert "an unknown label" (raises? (lambda () (exact-cover-choose st 7))))))

(test-group "Branching step"
  (let ((st (make-exact-cover knuth-options)))
    (test "first item with the fewest options, and its options" '(0 (2 4))
          (branch-of st))
    (test "one state per option" '((2) (4))
          (map exact-cover-chosen (exact-cover-step st)))
    (test "dead end: an item without options" '(4 ())
          (branch-of (exact-cover-choose* st '(2 3))))
    (test "complete: no item" '(#f ())
          (branch-of (exact-cover-choose* st '(4 1 5))))
    (test "no states after a complete one" '()
          (exact-cover-step (exact-cover-choose* st '(4 1 5))))))

;;; ==================================================================
;;; Search
;;; ==================================================================

(test-group "Knuth's example"
  (let ((st (make-exact-cover knuth-options)))
    (test "the one solution, in the order chosen" '((4 1 5)) (solutions-of st))
    ;; Root; option 2, then 3 (dead end); option 4, then 1, then 5.
    (test "search counts" '((nodes . 6) (guesses . 2) (updates . 12)) (stats-of st))
    (test "search from a chosen option" '((4 1 5))
          (solutions-of (exact-cover-choose st 4)))
    (test "search from a dead end" '() (solutions-of (exact-cover-choose st 2)))))

(test-group "Forced search"
  (let ((st (make-exact-cover '((a 0 1) (b 2)))))
    (test "solution" '((a b)) (solutions-of st))
    (test "no guesses" '((nodes . 3) (guesses . 0) (updates . 2)) (stats-of st))))

(test-group "No solution"
  (test "an item in no option" 0 (count-of (make-exact-cover '((a 0) (b 1)) primary: 3)))
  (test "overlapping options only" 0 (count-of (make-exact-cover '((a 0 1) (b 1 2))))))

(test-group "Several bit-set words"
  ;; Items 0 .. 199 in pairs (2j, 2j+1), each pair covered by option
  ;; (a j) or by the two options (b j) and (c j); 2^100 solutions in all.
  ;; Choosing (a j) for j >= 2 leaves 4 solutions.
  (let* ((options (append-map (lambda (j)
                                (list (list (list 'a j) (* 2 j) (+ 1 (* 2 j)))
                                      (list (list 'b j) (* 2 j))
                                      (list (list 'c j) (+ 1 (* 2 j)))))
                              (iota 100)))
         (st (make-exact-cover options))
         (chosen (exact-cover-choose* st (map (lambda (j) (list 'a j)) (iota 98 2)))))
    (test "items" 200 (exact-cover-item-count st))
    (test "options" 300 (exact-cover-option-count st))
    (test "items left after the choices" '(0 1 2 3) (exact-cover-uncovered chosen))
    (test "options left after the choices" 6 (exact-cover-option-count chosen))
    (test "options removed by a choice across words" '(((c 70)) ((a 70) (b 70)))
          (let ((s1 (exact-cover-choose st '(b 70))))
            (list (filter (lambda (l) (equal? (cadr l) 70)) (exact-cover-available s1))
                  (lset-difference equal? (exact-cover-available st) (exact-cover-available s1)))))
    (test "solutions left" 4 (count-of chosen))
    (test-assert "the last option conflicts with itself only through its items"
                 (not (exact-cover-choose (exact-cover-choose st '(a 99)) '(c 99))))))

(test-group "Counting solutions"
  (test "4 queens" 2 (count-of (queens 4)))
  (test "5 queens" 10 (count-of (queens 5)))
  (test "6 queens" 4 (count-of (queens 6)))
  (test "8 queens" 92 (count-of (queens 8)))
  (test "domino tilings of 2x4" 5 (count-of (dominoes 2 4)))
  (test "domino tilings of 3x4" 11 (count-of (dominoes 3 4)))
  (test "domino tilings of 4x4" 36 (count-of (dominoes 4 4)))
  (test "counting stops at the limit" 7 (count-of (queens 5) limit: 7))
  (test "solutions stop at the limit" 3 (length (solutions-of (queens 5) limit: 3)))
  (test-assert "the limit must be positive"
               (raises? (lambda () (exact-cover-count (queens 4) limit: 0)))))

(test-group "Secondary items"
  (let ((sols (solutions-of (queens 4))))
    (test "4 queens solutions" '(((0 . 1) (1 . 3) (2 . 0) (3 . 2))
                                 ((0 . 2) (1 . 0) (2 . 3) (3 . 1)))
          (map (lambda (s) (sort s (lambda (a b) (< (car a) (car b))))) sols)))
  (test "an option of secondary items only is never needed" 1
        (count-of (make-exact-cover '((a 0) (s 1)) primary: 1))))

(test-group "Branch items"
  (let ((plain (solutions-of (queens 6)))
        (rows (solutions-of (make-exact-cover
                             (append-map (lambda (r)
                                           (map (lambda (c)
                                                  (list (cons r c) r (+ 6 c) (+ 12 r c)
                                                        (+ 23 r (- c) 5)))
                                                (iota 6)))
                                         (iota 6))
                             primary: 12 branch-items: (iota 6)))))
    (test "same solutions when branching on rows only"
          (sorted-solutions plain) (sorted-solutions rows))
    ;; Item 0 has two options, items 1 and 2 one each.
    (test "without branch items: the item with the fewest options" '(1 (c))
          (branch-of (make-exact-cover '((a 0 2) (b 0) (c 1)))))
    (test "with branch items: a branch item, though another has fewer options" '(0 (a b))
          (branch-of (make-exact-cover '((a 0 2) (b 0) (c 1)) branch-items: '(0))))
    (test "branch items all covered: the other items" '(1 (c))
          (branch-of (exact-cover-choose
                      (make-exact-cover '((a 0 2) (b 0) (c 1)) branch-items: '(0))
                      'a)))))

(test-group "Shuffled search"
  (let ((reverse-order (lambda (xs) (reverse xs))))
    (test "same tilings in another order"
          (sorted-solutions (solutions-of (dominoes 3 4)))
          (sorted-solutions (solutions-of (dominoes 3 4) shuffle: reverse-order)))
    (test-assert "the order of solutions changes"
                 (not (equal? (solutions-of (dominoes 3 4))
                              (solutions-of (dominoes 3 4) shuffle: reverse-order))))))

(test-exit)
