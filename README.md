# exact-cover

Exact cover problems for CHICKEN 6, solved by a purely functional
version of Knuth's Algorithm X.

An exact cover problem has a set of items and a list of options, each
option a set of items. A solution is a choice of options such that every
primary item lies in exactly one chosen option and every secondary item
in at most one. Sudoku, the n queens problem, polyomino tilings and
Latin squares all take this form.

## Design

The search picks an uncovered primary item contained in the fewest
available options, branches on each of those options, and in each branch
removes the options that share an item with the chosen one. An item with
one option is therefore covered at once (a forced move), and an item with
none ends the branch.

Instead of the dancing-links data structure, which unlinks and relinks
options in place, the search works on immutable states, following the
design of the Haskell [set-cover](https://hackage.haskell.org/package/set-cover)
library by Henning Thielemann. A state holds the set of available
options, the set of uncovered primary items, the number of available
options containing each item, and the labels of the chosen options.
Choosing an option returns a new state and leaves the old one intact, so:

- nothing is undone on backtracking;
- a state can be searched more than once, or explored one step at a time;
- partial assignments (such as the givens of a puzzle) are made by
  choosing options before the search.

Item sets and option sets are bit sets (vectors of fixnum words). Each
option carries the set of options it conflicts with, computed once per
problem, so a choice is one set difference plus an update of the counts
of the items of the removed options.

## API

### Problems and states

`(make-exact-cover OPTIONS #!key primary branch-items)` returns the
initial state. `OPTIONS` is a list of `(LABEL ITEM ...)`: a label (any
value, distinct under `equal?`) and one or more items (non-negative
integers). Items below `primary` must be covered exactly once, the others
at most once (default: all items primary). `branch-items` is a list of
primary items to branch on in preference to the others.

- `(exact-cover-choose STATE LABEL)`: the state after choosing that
  option, or `#f` if it conflicts with an option already chosen.
- `(exact-cover-choose* STATE LABELS)`: several choices in turn.
- `(exact-cover-branch STATE)`: two values, the item the search would
  branch on (`#f` when complete) and the labels of its options (empty at a
  dead end).
- `(exact-cover-step STATE)`: the list of child states.
- `exact-cover-chosen`, `exact-cover-uncovered`, `exact-cover-available`,
  `exact-cover-complete?`, `exact-cover-item-count`,
  `exact-cover-option-count`.

### Search

- `(exact-cover-fold STATE KONS KNIL #!key limit shuffle)`: folds
  `(KONS labels acc)` over the solutions (labels in the order chosen),
  stopping after `limit` solutions. `shuffle`, a procedure reordering a
  list, sets the order in which the options of each branch are tried
  (for example a random order). Returns the result and the search
  statistics.
- `(exact-cover-solutions STATE #!key limit shuffle)`: the list of
  solutions and the statistics.
- `(exact-cover-count STATE #!key limit)`: the number of solutions and
  the statistics.

The statistics (`search-stats-nodes`, `search-stats-guesses`,
`search-stats-updates`, `search-stats->alist`) count the states visited,
the states entered through a choice among two or more options, and the
options removed by the choices. They serve as measures of difficulty.

## Example

```scheme
(import exact-cover)

;; Knuth's example: items A .. G are 0 .. 6.
(define st (make-exact-cover '((1 2 4 5) (2 0 3 6) (3 1 2 5)
                               (4 0 3) (5 1 6) (6 3 4 6))))
(exact-cover-solutions st)     ; => ((4 1 5)), stats

;; Eight queens: rows and columns primary, diagonals secondary.
(define (queens n)
  (make-exact-cover
   (append-map (lambda (r)
                 (map (lambda (c)
                        (list (cons r c) r (+ n c) (+ (* 2 n) r c)
                              (+ (* 4 n) -1 r (- c) n -1)))
                      (iota n)))
               (iota n))
   primary: (* 2 n)))
(exact-cover-count (queens 8))  ; => 92, stats
```

## Examples

`examples/graph-grid-layout.scm` draws a small graph in three stages:
a force-directed layout (Fruchterman-Reingold), then two exact cover
problems.

- Grid snapping: each node moves to one of its k nearest lattice points,
  no two nodes to the same point (nodes primary, lattice points
  secondary); k grows until a placement exists, and the placement with
  the least squared displacement is kept.
- Orthogonal edge routing: each edge chooses one of its candidate grid
  paths (bounded detour and number of bends) so that no two edges share a
  grid segment or bend at the same point (edges primary, segments and
  bend points secondary); the limits grow until a routing exists, and the
  routing with the least length plus bends is kept.

The result is printed as text and checked against these rules.

```
csi -s examples/graph-grid-layout.scm
```

## Building and testing

```
chicken-install -test
```

The tests use the `test` egg (`tests/run.scm`).

## License

LGPL-3.
