;;;; graph-grid-layout.scm - grid layout and orthogonal edge routing of a graph
;;;
;;; A drawing of a graph in three stages, the last two of them exact
;;; cover problems:
;;;
;;;   1. Force-directed layout (Fruchterman and Reingold): node positions
;;;      as real coordinates, found by simulating springs on the edges
;;;      and repulsion between all nodes.
;;;
;;;   2. Grid snapping: every node moves to a point of a coarse lattice,
;;;      no two nodes to the same point.  The options of a node are its k
;;;      nearest lattice points; the nodes are primary items and the
;;;      lattice points secondary ones.  k grows from 1 until a placement
;;;      exists, and among the placements for that k the one that moves
;;;      the nodes least (sum of squared distances) is kept.
;;;
;;;   3. Orthogonal edge routing: every edge becomes a path of horizontal
;;;      and vertical unit segments on a fine grid, in which the lattice
;;;      points of stage 2 are every s-th grid point.  The options of an
;;;      edge are its candidate paths: simple paths between its end nodes
;;;      that pass through no other node, are at most `slack' steps longer
;;;      than the shortest possible, and bend at most `bends' times.  The
;;;      edges are primary items; every grid segment is a secondary item
;;;      (two edges never share a segment), and so is every grid point as
;;;      a place to bend (two edges never turn at the same point, which
;;;      would draw as touching corners).  Edges may cross at a point
;;;      where both go straight.  The slack and bend limits grow until a
;;;      routing exists, and the routing with the least total length plus
;;;      bends is kept.
;;;
;;; The search always branches on the edge with the fewest candidate
;;; paths left, which is the "most constrained net first" rule of
;;; circuit routers.
;;;
;;; Usage: csi -s examples/graph-grid-layout.scm

(import scheme
        (only (scheme base) vector-map vector-for-each string-copy)
        (chicken base)
        (chicken format)
        (chicken sort)
        (srfi 1)
        exact-cover)

;;; ==================================================================
;;; The graph
;;; ==================================================================

;; A small office network: node name and the character it is drawn with.
(define nodes
  '((gw . #\G) (fw . #\F) (core . #\C) (sw1 . #\1) (sw2 . #\2)
    (srv . #\S) (db . #\D) (ap . #\A) (nas . #\N)))

(define edges
  '((gw fw) (fw core) (fw srv) (core sw1) (core sw2) (core nas)
    (sw1 srv) (sw1 db) (srv db) (sw2 ap) (sw2 nas)))

(define n-nodes (length nodes))

(define (node-index name)
  (or (list-index (lambda (n) (eq? (car n) name)) nodes)
      (error "unknown node" name)))

(define (node-char v) (cdr (list-ref nodes v)))

(define edge-ends
  (list->vector (map (lambda (e) (cons (node-index (car e)) (node-index (cadr e)))) edges)))

(define n-edges (vector-length edge-ends))

;;; ==================================================================
;;; 1. Force-directed layout
;;; ==================================================================

;; Fruchterman-Reingold with an ideal edge length suited to the unit
;; square, starting from the nodes on a circle, so that the result needs
;; no random numbers.  Returns a vector of (x . y) pairs.
(define (force-layout iterations)
  (let* ((n n-nodes)
         (k (sqrt (/ 1.0 n)))
         (pos (list->vector
               (map (lambda (i)
                      (let ((a (/ (* 2 3.141592653589793 i) n)))
                        (cons (+ 0.5 (* 0.4 (cos a))) (+ 0.5 (* 0.4 (sin a))))))
                    (iota n)))))
    (do ((it 0 (+ it 1))) ((= it iterations) pos)
      (let ((t (* 0.1 (- 1.0 (/ it iterations))))
            (disp (make-vector n '(0.0 . 0.0))))
        (define (push! i fx fy)
          (let ((d (vector-ref disp i)))
            (vector-set! disp i (cons (+ (car d) fx) (+ (cdr d) fy)))))
        (define (between i j)
          ;; The vector from node j to node i and its length.
          (let* ((dx (- (car (vector-ref pos i)) (car (vector-ref pos j))))
                 (dy (- (cdr (vector-ref pos i)) (cdr (vector-ref pos j)))))
            (values dx dy (max 1e-6 (sqrt (+ (* dx dx) (* dy dy)))))))
        ;; Repulsion between every pair of nodes.
        (do ((i 0 (+ i 1))) ((= i n))
          (do ((j (+ i 1) (+ j 1))) ((= j n))
            (let-values (((dx dy d) (between i j)))
              (let ((f (/ (* k k) d d)))
                (push! i (* f dx) (* f dy))
                (push! j (- (* f dx)) (- (* f dy)))))))
        ;; Attraction along the edges.
        (vector-for-each
         (lambda (e)
           (let-values (((dx dy d) (between (car e) (cdr e))))
             (let ((f (/ d k)))
               (push! (car e) (- (* f dx)) (- (* f dy)))
               (push! (cdr e) (* f dx) (* f dy)))))
         edge-ends)
        ;; Move each node along its displacement, by at most t.
        (do ((i 0 (+ i 1))) ((= i n))
          (let* ((d (vector-ref disp i))
                 (len (max 1e-9 (sqrt (+ (* (car d) (car d)) (* (cdr d) (cdr d))))))
                 (step (min len t))
                 (p (vector-ref pos i)))
            (vector-set! pos i (cons (+ (car p) (* step (/ (car d) len)))
                                     (+ (cdr p) (* step (/ (cdr d) len)))))))))))

;;; ==================================================================
;;; 2. Grid snapping
;;; ==================================================================

;; Scales the positions so that their bounding box fills a lattice of
;; COLS x ROWS points (coordinates 0 .. COLS-1 and 0 .. ROWS-1, row 0 at
;; the top).
(define (scale-to-lattice pos cols rows)
  (let* ((xs (map car (vector->list pos)))
         (ys (map cdr (vector->list pos)))
         (x0 (apply min xs)) (x1 (apply max xs))
         (y0 (apply min ys)) (y1 (apply max ys)))
    (vector-map (lambda (p)
                  (cons (* (- cols 1) (/ (- (car p) x0) (max 1e-9 (- x1 x0))))
                        ;; Rows count downwards, y upwards.
                        (* (- rows 1) (/ (- y1 (cdr p)) (max 1e-9 (- y1 y0))))))
                pos)))

(define (squared-distance p q)
  (let ((dx (- (car p) (car q))) (dy (- (cdr p) (cdr q))))
    (+ (* dx dx) (* dy dy))))

;; The K lattice points nearest to P, nearest first.
(define (nearest-points p k cols rows)
  (take (sort (append-map (lambda (y) (map (lambda (x) (cons x y)) (iota cols))) (iota rows))
              (lambda (a b) (< (squared-distance a p) (squared-distance b p))))
        k))

;; Keeps the cheaper of the best so far and a new solution: the
;; accumulator of the folds below is (count . best), best being
;; (cost . labels) or #f.
(define (keep-cheapest cost)
  (lambda (labels acc)
    (let ((c (cost labels))
          (best (cdr acc)))
      (cons (+ 1 (car acc))
            (if (or (not best) (< c (car best))) (cons c labels) best)))))

;; Places every node on its own lattice point.  Returns the lattice point
;; of every node (a vector), the k used, the number of placements
;; compared, the total squared displacement and the search statistics.
(define (snap-to-lattice scaled cols rows)
  (let try ((k 1))
    (when (> k (* cols rows))
      (error "no placement on the lattice"))
    (let* ((options
            (append-map
             (lambda (v)
               (map (lambda (q)
                      ;; Label (node . point); items: the node, then its point.
                      (list (cons v q) v (+ n-nodes (* (cdr q) cols) (car q))))
                    (nearest-points (vector-ref scaled v) k cols rows)))
             (iota n-nodes)))
           (cost (lambda (labels)
                   (fold (lambda (l s) (+ s (squared-distance (cdr l) (vector-ref scaled (car l)))))
                         0 labels))))
      (let-values (((acc stats)
                    (exact-cover-fold (make-exact-cover options primary: n-nodes)
                                      (keep-cheapest cost) (cons 0 #f)
                                      limit: 20000)))
        (match-best acc
                    (lambda (best)
                      (let ((points (make-vector n-nodes)))
                        (for-each (lambda (l) (vector-set! points (car l) (cdr l))) (cdr best))
                        (values points k (car acc) (car best) stats)))
                    (lambda () (try (+ k 1))))))))

(define (match-best acc found none)
  (if (cdr acc) (found (cdr acc)) (none)))

;;; ==================================================================
;;; 3. Orthogonal edge routing
;;; ==================================================================

;; The fine grid has W x H points; node v sits at S times its lattice
;; point.  Items: edges 0 .. E-1 (primary), then the horizontal
;; segments, the vertical segments and the bend points (secondary).

(define (make-grid cols rows s)
  (let ((W (+ 1 (* s (- cols 1))))
        (H (+ 1 (* s (- rows 1)))))
    (list W H s)))

(define (grid-W g) (car g))
(define (grid-H g) (cadr g))
(define (grid-s g) (caddr g))

(define (h-segment-item g x y) (+ n-edges (* y (- (grid-W g) 1)) x))
(define (v-segment-item g x y)
  (+ n-edges (* (- (grid-W g) 1) (grid-H g)) (* y (grid-W g)) x))
(define (bend-item g x y)
  (+ n-edges (* (- (grid-W g) 1) (grid-H g)) (* (grid-W g) (- (grid-H g) 1))
     (* y (grid-W g)) x))

(define (segment-item g p q)
  (if (= (cdr p) (cdr q))
      (h-segment-item g (min (car p) (car q)) (cdr p))
      (v-segment-item g (car p) (min (cdr p) (cdr q)))))

(define (manhattan p q) (+ (abs (- (car p) (car q))) (abs (- (cdr p) (cdr q)))))

(define directions '((1 . 0) (-1 . 0) (0 . 1) (0 . -1)))

;; The simple paths from FROM to TO (lists of points, FROM first) that
;; avoid the points in BLOCKED, have at most MAX-LENGTH steps and bend at
;; most MAX-BENDS times.
(define (candidate-paths g from to blocked max-length max-bends)
  (let search ((p from) (dir #f) (len 0) (bends 0) (path (list from)) (acc '()))
    (if (equal? p to)
        (cons (reverse path) acc)
        (fold (lambda (d acc)
                (let ((q (cons (+ (car p) (car d)) (+ (cdr p) (cdr d))))
                      (bends (if (and dir (not (equal? d dir))) (+ bends 1) bends)))
                  (if (and (< -1 (car q) (grid-W g))
                           (< -1 (cdr q) (grid-H g))
                           (<= bends max-bends)
                           (<= (+ len 1 (manhattan q to)) max-length)
                           (not (member q path))
                           (or (equal? q to) (not (member q blocked))))
                      (search q d (+ len 1) bends (cons q path) acc)
                      acc)))
              acc
              directions))))

(define (bend-points path)
  ;; The interior points of PATH at which it changes direction.
  (let loop ((ps path) (acc '()))
    (if (or (null? ps) (null? (cdr ps)) (null? (cddr ps)))
        (reverse acc)
        (let ((a (car ps)) (b (cadr ps)) (c (caddr ps)))
          (loop (cdr ps)
                (if (or (= (car a) (car b) (car c)) (= (cdr a) (cdr b) (cdr c)))
                    acc
                    (cons b acc)))))))

(define (path-cost path) (+ (- (length path) 1) (length (bend-points path))))

(define (path-items g e path)
  (append (list e)
          (map (lambda (p q) (segment-item g p q)) path (cdr path))
          (map (lambda (b) (bend-item g (car b) (cdr b))) (bend-points path))))

;; Candidate paths of every edge (a vector of lists, cheapest first).
(define (edge-candidates g points slack bends)
  (let ((fine (vector-map (lambda (q) (cons (* (grid-s g) (car q)) (* (grid-s g) (cdr q))))
                          points)))
    (vector-map
     (lambda (e)
       (let* ((from (vector-ref fine (car e)))
              (to (vector-ref fine (cdr e)))
              (blocked (filter (lambda (q) (not (or (equal? q from) (equal? q to))))
                               (vector->list fine))))
         (sort (candidate-paths g from to blocked (+ (manhattan from to) slack) bends)
               (lambda (a b) (< (path-cost a) (path-cost b))))))
     edge-ends)))

;; The most routings compared at one level; the best of those is kept.
(define route-limit 2000)

;; Routes every edge, raising the slack and bend limits until a routing
;; exists.  Returns the paths (a vector, one per edge), the limits used,
;; the number of candidate paths, the number of routings compared, the
;; total cost and the search statistics; prints each level tried.
(define (route-edges g points)
  (let try ((levels '((0 1) (0 2) (2 2) (2 3) (4 3) (4 4) (6 4))))
    (when (null? levels)
      (error "no routing within the limits tried"))
    (let* ((slack (caar levels))
           (bends (cadar levels))
           (candidates (edge-candidates g points slack bends))
           (n-candidates (apply + (map length (vector->list candidates)))))
      (if (any null? (vector->list candidates))
          (begin
            (printf "  slack ~A, bends ~A: ~A candidate paths, some edge has none~%"
                    slack bends n-candidates)
            (try (cdr levels)))
          (let* ((options
                  (append-map (lambda (e)
                                (map (lambda (path) (cons (cons e path) (path-items g e path)))
                                     (vector-ref candidates e)))
                              (iota n-edges)))
                 (cost (lambda (labels) (fold (lambda (l s) (+ s (path-cost (cdr l)))) 0 labels))))
            (let-values (((acc stats)
                          (exact-cover-fold (make-exact-cover options primary: n-edges)
                                            (keep-cheapest cost) (cons 0 #f)
                                            limit: route-limit)))
              (printf "  slack ~A, bends ~A: ~A candidate paths, ~A routing(s) compared~A~%"
                      slack bends n-candidates (car acc)
                      (if (= (car acc) route-limit) " (search limit reached)" ""))
              (match-best acc
                          (lambda (best)
                            (let ((paths (make-vector n-edges)))
                              (for-each (lambda (l) (vector-set! paths (car l) (cdr l)))
                                        (cdr best))
                              (values paths slack bends n-candidates (car acc) (car best) stats)))
                          (lambda () (try (cdr levels))))))))))

;;; ==================================================================
;;; Drawing and checks
;;; ==================================================================

;; A text picture of the routed graph: grid point (x, y) is at column 2x
;; and row 2y, segments between them; '.' marks a free lattice point.
(define (draw g points paths)
  (let* ((W (grid-W g)) (H (grid-H g)) (s (grid-s g))
         (canvas (list->vector (map (lambda (r) (make-string (- (* 2 W) 1) #\space))
                                    (iota (- (* 2 H) 1)))))
         (ref (lambda (col row) (string-ref (vector-ref canvas row) col)))
         (put! (lambda (col row ch) (string-set! (vector-ref canvas row) col ch))))
    (do ((y 0 (+ y s))) ((>= y H))
      (do ((x 0 (+ x s))) ((>= x W))
        (put! (* 2 x) (* 2 y) #\.)))
    (vector-for-each
     (lambda (path)
       (for-each (lambda (p q)
                   (put! (+ (car p) (car q)) (+ (cdr p) (cdr q))
                         (if (= (cdr p) (cdr q)) #\- #\|)))
                 path (cdr path))
       (for-each (lambda (a b c)
                   (let ((ch (cond ((= (cdr a) (cdr b) (cdr c)) #\-)
                                   ((= (car a) (car b) (car c)) #\|)
                                   (else #\+)))
                         (old (ref (* 2 (car b)) (* 2 (cdr b)))))
                     (put! (* 2 (car b)) (* 2 (cdr b))
                           (if (memv old '(#\- #\| #\+)) #\+ ch))))
                 path (cdr path) (cddr path)))
     paths)
    (vector-for-each (lambda (q v) (put! (* 2 s (car q)) (* 2 s (cdr q)) (node-char v)))
                     points (list->vector (iota n-nodes)))
    (for-each (lambda (row) (printf "    ~A~%" row)) (vector->list canvas))))

;; Checks the result against the rules of the drawing; returns a list of
;; problems found (empty when all is well).
(define (check g points paths)
  (let* ((s (grid-s g))
         (fine (map (lambda (q) (cons (* s (car q)) (* s (cdr q)))) (vector->list points)))
         (segments (append-map (lambda (path) (map (lambda (p q) (segment-item g p q))
                                                   path (cdr path)))
                               (vector->list paths)))
         (bends (append-map bend-points (vector->list paths)))
         (problems '()))
    (define (problem! msg) (set! problems (cons msg problems)))
    (unless (= n-nodes (length (delete-duplicates (vector->list points))))
      (problem! "two nodes on one lattice point"))
    (vector-for-each
     (lambda (e path)
       (let ((from (list-ref fine (car e))) (to (list-ref fine (cdr e))))
         (unless (and (equal? (first path) from) (equal? (last path) to))
           (problem! (sprintf "edge ~A does not join its nodes" e)))
         (unless (every (lambda (p q) (= 1 (manhattan p q))) path (cdr path))
           (problem! (sprintf "edge ~A is not a grid path" e)))
         (unless (= (length path) (length (delete-duplicates path)))
           (problem! (sprintf "edge ~A visits a point twice" e)))
         (when (any (lambda (p) (member p fine)) (cdr (drop-right path 1)))
           (problem! (sprintf "edge ~A passes through a node" e)))))
     edge-ends paths)
    (unless (= (length segments) (length (delete-duplicates segments)))
      (problem! "two edges share a segment"))
    (unless (= (length bends) (length (delete-duplicates bends)))
      (problem! "two edges bend at the same point"))
    (reverse problems)))

;;; ==================================================================
;;; Main
;;; ==================================================================

(define cols 5)
(define rows 4)
(define spacing 3)

(printf "Graph: ~A nodes, ~A edges~%~%" n-nodes n-edges)

(define positions (force-layout 300))

(printf "1. Force-directed layout:~%")
(vector-for-each (lambda (n p) (printf "    ~A ~A  (~A, ~A)~%" (cdr n) (car n)
                                       (/ (round (* 100 (car p))) 100)
                                       (/ (round (* 100 (cdr p))) 100)))
                 (list->vector nodes) positions)

(printf "~%2. Snapping to a ~Ax~A lattice~%" cols rows)
(define-values (points snap-k snap-count snap-cost snap-stats)
  (snap-to-lattice (scale-to-lattice positions cols rows) cols rows))
(printf "  each node chooses among its ~A nearest point(s); ~A placement(s) compared~%"
        snap-k snap-count)
(printf "  total squared displacement ~A; search ~S~%"
        (/ (round (* 100 snap-cost)) 100) (search-stats->alist snap-stats))

(define grid (make-grid cols rows spacing))

(printf "~%3. Routing on a ~Ax~A grid (lattice spacing ~A)~%"
        (grid-W grid) (grid-H grid) spacing)
(define-values (paths slack bends n-candidates route-count route-cost route-stats)
  (route-edges grid points))
(printf "  routed with slack ~A and at most ~A bends per edge; total length + bends ~A~%"
        slack bends route-cost)
(printf "  search ~S~%~%" (search-stats->alist route-stats))

(draw grid points paths)

(let ((problems (check grid points paths)))
  (printf "~%~A~%" (if (null? problems)
                       "Checks passed: distinct node points, paths join their nodes, no shared segments or bend points."
                       (sprintf "Problems: ~S" problems))))
