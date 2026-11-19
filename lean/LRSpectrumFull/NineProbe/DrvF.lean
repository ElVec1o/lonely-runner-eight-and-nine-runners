/-
# Nine runners, part 13: table-valued drivers for the per-prime replay modules

No Mathlib import.  Nothing here is a claim about the lonely runner conjecture; the statements about these
definitions are in `NineSound/DrvFSound.lean`.

Why: `NineProbe.Drv` reads the level-1 descriptor table and the level-1 stream table as `gtab L i = L.getD i _`
with `L` a list of up to 20,000 entries.  The kernel evaluates `List.getD` by walking the list, so a lookup of the
tree with global index `i` costs about `i` steps, and every task or tree chunk checked late in the DFS order pays for
the whole prefix (peak memory of the chunk check grows with the chunk's index, 0.6 GB to 8.4 GB at p = 61).
Here the tables are functions `T : Nat -> alpha` that the generator emits as a balanced tree of definitions
(`bif Nat.ble mid i then right i else left i`, logarithmic depth), clamped to the last entry beyond `N`.

* `clampT T N i`      `T (min i (N - 1))`
* `ctT S N k`         the blobs of tree `k`: blob `i` of the stream `S` of tree `k` (default 0)
* `allRootsF`         `checkRootN` over the trees `k, .., k + n - 1`, with the streams, the nx-table and the descriptors given as functions
-/

import LRSpectrumFull.NineProbe.Check

namespace LRSpectrumFull.NineProbe

/-- entry `min i (N - 1)` of the table `T` -/
def clampT {α : Type} (T : Nat → α) (N i : Nat) : α :=
  T (bif Nat.ble i (Nat.sub N 1) then i else Nat.sub N 1)

/-- blob `i` of the stream of tree `k` (default 0) -/
def ctT (S : Nat → List Nat) (N k : Nat) : Nat → Nat := fun i => (clampT S N k).getD i 0

/-- `checkRootN` holds for the trees `k, .., k + n - 1` with streams `CT` and descriptors `Dk` -/
def allRootsF (X : Ctx) (CT : Nat → Nat → Nat) (nx : Nat → Nat × Nat × Nat) (Dk : Nat → Nat × Nat × Nat) :
    Nat → Nat → Bool
  | _, 0 => true
  | k, n + 1 => checkRootN X (CT k) nx (Dk k) && allRootsF X CT nx Dk (k + 1) n

end LRSpectrumFull.NineProbe
