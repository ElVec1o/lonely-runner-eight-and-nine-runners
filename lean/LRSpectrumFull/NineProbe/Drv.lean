/-
# Nine runners, part 8: light driver definitions for the per-prime replay modules

No Mathlib import (the generated data and check modules must stay cheap to import).  Nothing here is a claim
about the lonely runner conjecture; the statements about these definitions are in `NineSound/DrvSound.lean`.

* `gtab L i`           entry `i` of the list `L`; out of range it is the head (or `default`).  Every generated
                       table (`H`, `nx1`, `nx2`) is `gtab` of a list, so "every index hits an entry below the
                       length" (clauses a3, a4, a5) is one generic lemma (`gtab_surj`).
* `tkC`, `tkH`         the certificate blobs and the delegated state of task `k` in a task list
* `ctOf`               the certificate blobs of tree `k` in a list of streams
* `allTasks`, `allRoots`  the Boolean conjunction of `checkTask` (resp. `checkRootN`) over the tasks (trees)
                       `k, k+1, .., k+n-1`; one `decide +kernel` theorem per generated chunk module.
-/

import LRSpectrumFull.NineProbe.Check

namespace LRSpectrumFull.NineProbe

instance : Inhabited St := ⟨noH 0⟩

/-- entry `i` of `L`, with the head as default -/
def gtab {α : Type} [Inhabited α] (L : List α) (i : Nat) : α := L.getD i (L.headD default)

/-- task `τ` (clamped to `nT - 1`) of a chunked task table: `CH` the chunks (each a local list), `starts` their first
global indices.  Only the chunk of `τ` is ever unfolded. -/
def tcOf (CH : List (List (St × List Nat))) (starts : List Nat) (nT τ : Nat) : St × List Nat :=
  let t := min τ (nT - 1)
  let c := (starts.filter (fun s => Nat.ble s t)).length - 1
  gtab (gtab CH c) (t - starts.getD c 0)

/-- blobs of the task `τ` -/
def tkC (CH : List (List (St × List Nat))) (starts : List Nat) (nT τ : Nat) : Nat → Nat :=
  fun i => ((tcOf CH starts nT τ).2).getD i 0

/-- delegated state of the task `τ` -/
def tkH (CH : List (List (St × List Nat))) (starts : List Nat) (nT τ : Nat) : St := (tcOf CH starts nT τ).1

/-- blobs of the tree `k` of a list of streams -/
def ctOf (L : List (List Nat)) (k : Nat) : Nat → Nat := fun i => (gtab L k).getD i 0

/-- `checkTask` holds for the tasks `k, .., k + n - 1` -/
def allTasks (X : Ctx) (CH : List (List (St × List Nat))) (starts : List Nat) (nT : Nat) (H : Nat → St)
    (nx : Nat → Nat × Nat × Nat) : Nat → Nat → Bool
  | _, 0 => true
  | k, n + 1 => checkTask X (tkC CH starts nT k) nx (H k) && allTasks X CH starts nT H nx (k + 1) n

/-- `checkRootN` holds for the trees `k, .., k + n - 1` with descriptors from `D` -/
def allRoots (X : Ctx) (L : List (List Nat)) (nx : Nat → Nat × Nat × Nat) (D : List (Nat × Nat × Nat)) :
    Nat → Nat → Bool
  | _, 0 => true
  | k, n + 1 => checkRootN X (ctOf L k) nx (gtab D k) && allRoots X L nx D (k + 1) n

end LRSpectrumFull.NineProbe
