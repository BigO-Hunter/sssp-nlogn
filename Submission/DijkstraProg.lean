import Frontier.CostModel
import Frontier.RAMWitness

/-!
# Submission.DijkstraProg — the row program text (B1, R2125608239)

A uniform `Frontier.RAM.Program` at `wordExp = 0` (words below `n + m + 2`):

`P = ite (m/n ≤ pa) dijkstra bfBody` where `pa = ⌊log₂ n⌋` is computed by a
halving loop, `bfBody` is the fork's verified Bellman–Ford text
(`Frontier.RAM.BF.prog`, spliced verbatim; `InputFrame` was designed for this),
and `dijkstra` is a lazy binary-heap Dijkstra over adjacency lists.

Design notes (cap-safety at wordExp = 0):
* heap arrays `hv hd` have length `m + 1` (at most `m + 1` inserts: one initial
  push and at most one per edge scan); all heap indices are `< m + 1 < n + m + 2`;
* sift-down child indices `2·ii + 1` are computed only inside the guard
  `ii + 1 ≤ h / 2`, which forces `2·ii + 1 < h ≤ m + 1`, so the `add` evaluations
  always fit; the guard itself uses only `+1` and `/2`;
* adjacency lists `head n` / `nxt m` with the `e + 1` encoding (0 = nil);
* `m / n ≤ pa` is the dispatch test (equivalent to `m ≤ n·pa` up to `n`, and
  every graph with `m ≤ n·⌊log₂ n⌋` — the row cap — takes the Dijkstra branch).
  The division is stuck for `n = 0`, which is vacuous (there is no `s : Fin G.n`);
* the heap extracts the true minimum (lazy inserts, `done`-skips); no
  arbitrary-extraction shortcut (cf. the counterexample on R2125608238 riders).

This file is text only: no lemmas. The proofs live in `DijkstraSim`.
-/

namespace Submission.DijkstraProg

open Frontier.RAM WExpr Stmt

/-- `pa := ⌊log₂ n⌋`, `t := n / 2^pa` by halving. -/
def calcPa : Stmt :=
  seq (wset "t" (var "n"))
    (seq (wset "pa" (lit 0))
      (.while (lt (lit 1) (var "t"))
        (seq (wset "t" (div (var "t") (lit 2))) (wset "pa" (add (var "pa") (lit 1))))))

/-- Sift `ii` toward the root while the parent key is larger (min-heap, `≤` ties move up). -/
def siftUp : Stmt :=
  .while (lt (lit 0) (var "ii"))
    (seq (wset "p" (div (sub (var "ii") (lit 1)) (lit 2)))
      (seq (vle "b" (.load "hd" (var "ii")) (.load "hd" (var "p")))
        (ite (var "b")
          (seq (vset "tv" (.load "hd" (var "ii")))
          (seq (vstore "hd" (var "ii") (.load "hd" (var "p")))
          (seq (vstore "hd" (var "p") (.var "tv"))
          (seq (wset "tw" (load "hv" (var "ii")))
          (seq (wstore "hv" (var "ii") (load "hv" (var "p")))
          (seq (wstore "hv" (var "p") (var "tw"))
               (wset "ii" (var "p"))))))))
          (wset "ii" (lit 0)))))

/-- One sift-down step from `ii` (left child exists; pick the smaller child, swap or stop). -/
def siftDownStep : Stmt :=
  seq (wset "cl" (add (add (var "ii") (var "ii")) (lit 1)))
    (seq (wset "c" (var "cl"))
      (seq (ite (lt (add (var "cl") (lit 1)) (var "h"))
            (seq (vle "b" (.load "hd" (add (var "cl") (lit 1))) (.load "hd" (var "cl")))
              (ite (var "b") (wset "c" (add (var "cl") (lit 1))) skip))
            skip)
        (seq (vle "b" (.load "hd" (var "c")) (.load "hd" (var "ii")))
          (ite (var "b")
            (seq (vset "tv" (.load "hd" (var "ii")))
            (seq (vstore "hd" (var "ii") (.load "hd" (var "c")))
            (seq (vstore "hd" (var "c") (.var "tv"))
            (seq (wset "tw" (load "hv" (var "ii")))
            (seq (wstore "hv" (var "ii") (load "hv" (var "c")))
            (seq (wstore "hv" (var "c") (var "tw"))
                 (wset "ii" (var "c"))))))))
            (wset "go" (lit 0))))))

/-- Sift `ii` down to a leaf. -/
def siftDown : Stmt :=
  seq (wset "ii" (lit 0)) (seq (wset "go" (lit 1))
    (.while (var "go")
      (ite (lt (add (var "ii") (lit 1)) (add (div (var "h") (lit 2)) (lit 1)))
        siftDownStep
        (wset "go" (lit 0)))))

/-- Push vertex `pv` with key `dist[pv]` (callers set `pv`). -/
def pushBody : Stmt :=
  seq (wstore "hv" (var "h") (var "pv"))
    (seq (vstore "hd" (var "h") (.load "dist" (var "pv")))
      (seq (wset "ii" (var "h"))
        (seq (wset "h" (add (var "h") (lit 1)))
          (seq (wset "ins" (add (var "ins") (lit 1))) siftUp))))

/-- Initial allocation of the six arrays. -/
def allocAll : Stmt :=
  seq (valloc "dist" (var "n"))
    (seq (walloc "reach" (var "n"))
      (seq (walloc "done" (var "n"))
        (seq (walloc "head" (var "n"))
          (seq (walloc "nxt" (var "m"))
            (seq (walloc "hv" (add (var "m") (lit 1)))
              (valloc "hd" (add (var "m") (lit 1))))))))

/-- Adjacency build: prepend each edge to `head[src[e]]`. -/
def buildAdj : Stmt :=
  seq (wset "e" (lit 0))
    (.while (lt (var "e") (var "m"))
      (seq (wset "u" (load "src" (var "e")))
        (seq (wset "q" (load "head" (var "u")))
          (seq (wstore "nxt" (var "e") (var "q"))
            (seq (wstore "head" (var "u") (add (var "e") (lit 1)))
              (wset "e" (add (var "e") (lit 1))))))))

/-- The relax of edge `e` (with `v = src e` settled and `x = dst e`): relax iff
`reach[x] = 0` or `cand < dist[x]`; push `x` if unsettled. -/
def relaxBody : Stmt :=
  seq (ite (eq (load "reach" (var "x")) (lit 0))
        (wset "fl" (lit 1))
        (seq (vle "b" (.load "dist" (var "x")) (.var "cand"))
          (ite (var "b") (wset "fl" (lit 0)) (wset "fl" (lit 1)))))
    (ite (var "fl")
      (seq (vstore "dist" (var "x") (.var "cand"))
        (seq (wstore "reach" (var "x") (lit 1))
          (ite (eq (load "done" (var "x")) (lit 0))
            (seq (wset "pv" (var "x")) pushBody)
            skip)))
      skip)

/-- Scan the out-edge chain of the settled vertex `v`, relaxing each edge. -/
def scanBody : Stmt :=
  .while (lt (lit 0) (var "q"))
    (seq (wset "e" (sub (var "q") (lit 1)))
      (seq (wset "q" (load "nxt" (var "e")))
        (seq (wset "x" (load "dst" (var "e")))
          (seq (vset "cand" (.add (.load "dist" (var "v")) (.load "w" (var "e"))))
            relaxBody))))

/-- Settle `v`: mark done and scan its out-edges. -/
def settleBody : Stmt :=
  seq (wstore "done" (var "v") (lit 1))
    (seq (wset "q" (load "head" (var "v"))) scanBody)

/-- Pop the min entry into `v`, shrink the heap, sift the hole down. -/
def popBody : Stmt :=
  seq (wset "v" (load "hv" (lit 0)))
    (seq (vset "dv" (.load "hd" (lit 0)))
      (seq (wset "h" (sub (var "h") (lit 1)))
        (ite (lt (lit 0) (var "h"))
          (seq (wstore "hv" (lit 0) (load "hv" (var "h")))
            (seq (vstore "hd" (lit 0) (.load "hd" (var "h"))) siftDown))
          skip)))

/-- The main loop: pop-min until the heap is empty; settle stale-free pops. -/
def mainLoop : Stmt :=
  .while (lt (lit 0) (var "h"))
    (seq popBody
      (ite (eq (load "done" (var "v")) (lit 0)) settleBody skip))

/-- The Dijkstra branch. -/
def dijkstraBody : Stmt :=
  seq allocAll
    (seq buildAdj
      (seq (wset "h" (lit 0))
        (seq (wset "ins" (lit 0))
          (seq (wset "pv" (var "s"))
            (seq pushBody mainLoop)))))

/-- The dispatch wrapper: `if m / n ≤ pa then dijkstra else Bellman–Ford`
(`¬ (pa < m / n)` as the test; `WExpr` has no `le`). -/
def prog : Stmt :=
  seq calcPa
    (ite (lt (var "pa") (div (var "m") (var "n"))) Frontier.RAM.BF.prog dijkstraBody)

/-- The row program (words below `n + m + 2`, no procedures). -/
def p1 : Program := { body := prog, wordExp := 0 }

end Submission.DijkstraProg
