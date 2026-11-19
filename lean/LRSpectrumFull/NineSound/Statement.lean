/-
# Nine runners, soundness part 1: the exact statement of the checker soundness theorem (statement first)

`Check9Sound` is the Lean `Prop` that the soundness proof (parts 2 to 7 of the development) must prove.  It is a DEFINITION (a proposition), not a theorem; no
`sorry` and no axiom is introduced.  It pins, for one prime `p`:

* `TableOK9`   what the generated context `X_i` (levels `i = 0, 1, 2`, moduli `p, 3p, 9p`) must encode: the
               window, the admissible classes, the side mask `m3` (multiples of 3), the `±c mod p` and
               `±c mod 3p` class masks of the pinned items (`row`), the coverer masks `cbJ`, the counter
               function `cntF`, and the low-class masks `lowp`, `lowT` used to canonicalise items;
* the replay   `checkTree0` (level 0, class 1 forced, with delegated subtrees `7 i` checked by `checkTask`),
               `checkRootN` for every level-1 tree (descriptor `nx1 k`) and every level-2 tree (`nx2 k`);
* the closure  every descriptor index named by a leaf record `5 i` is the descriptor of a checked tree
               (`hrange1`, `hrange2`: the generator builds `nx` as a balanced tree, so out-of-range indices
               return the last real descriptor), and every delegated state is one of the checked tasks.

The conclusion is `lemma7Check 8 p = true`, the property consumed by `e2_prime_dvd9`.  Nothing here is a
claim about the lonely runner conjecture until the theorem is proved.
-/

import LRSpectrumFull.NineSound.Proj
import LRSpectrumFull.NineSound.Fold
import LRSpectrumFull.NineProbe.Check
import LRSpectrumFull.EightCheckSound

namespace LRSpectrumFull.NineSound

open LRSpectrumFull LRSpectrumFull.NineProbe

/-- the multiplier of level `i`: moduli `p`, `3p`, `9p` -/
def lvlMult (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 3 else 9

/-- admissible classes at modulus `M`: `[1, M/2]` without the multiples of `p` -/
def AdmC (M p : ℕ) : Finset ℕ := (Win M).filter (fun v => v % p ≠ 0)

/-- `y ≡ ± c (mod m)` -/
def PM (m c y : ℕ) : Prop := y % m = c % m ∨ y % m + c % m = m

instance (m c y : ℕ) : Decidable (PM m c y) := by unfold PM; infer_instance

/-- the generated context `X` of level `i` at the prime `p` encodes the covering data of the level -/
def TableOK9 (X : Ctx) (i p : ℕ) : Prop :=
  X.lvl = i ∧ X.W = (lvlMult i * p) / 2 ∧
  X.full = EightV4.compactOf (Win (lvlMult i * p)) ∧
  X.adm = EightV4.spreadOf (AdmC (lvlMult i * p) p) ∧
  X.m3 = (if i = 0 then 0
      else EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun x => x % 3 = 0))) ∧
  X.ones = EightV4.spreadOf (Finset.range (X.W + 1)) ∧
  X.lowp = EightV4.spreadOf (Finset.Icc 1 ((p - 1) / 2)) ∧
  X.lowT = EightV4.spreadOf (Finset.Icc 1 ((3 * p - 1) / 2)) ∧
  (∀ x ∈ AdmC (lvlMult i * p) p, X.row (2 ^ (16 * x)) =
      (x, EightV4.compactOf ((Win (lvlMult i * p)).filter (fun j => covM (lvlMult i * p) j x)),
        (if 1 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM p x y)) else 0),
        (if 2 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM (3 * p) x y))
          else 0))) ∧
  (∀ j ∈ Win (lvlMult i * p), X.cbJ j =
      EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun x => covM (lvlMult i * p) j x))) ∧
  (∀ u acc, (∀ j, u.testBit j = true → j ∈ Win (lvlMult i * p)) →
    X.cntF u acc = acc + ∑ j ∈ (Win (lvlMult i * p)).filter (fun j => u.testBit j = true), X.cbJ j)

/-- **The soundness theorem to be proved** (K = 8, nine runners).  The data of one prime: contexts, the
level-0 certificate `C0` with its delegation table `H`, the delegated subtree certificates `Ct`, the level-1
and level-2 tree certificates `C1`, `C2` with their descriptor tables `nx1`, `nx2`. -/
def Check9Sound : Prop :=
  ∀ (p : ℕ), p.Prime → 11 < p →
  ∀ (X0 X1 X2 : Ctx), TableOK9 X0 0 p → TableOK9 X1 1 p → TableOK9 X2 2 p →
  ∀ (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ)
    (Ct C1 C2 : ℕ → ℕ → ℕ),
  checkTree0 X0 C0 H nx1 = true →
  (∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true) →
  (∀ i, ∃ τ, τ < nT ∧ H i = H τ) →
  (∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) →
  (∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k) →
  (∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true) →
  (∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true) →
  lemma7Check 8 p = true

/-- the two halves of the chain that ARE proved, packaged: for every prime passing the check, the prime
divides a speed of any primitive counterexample (`e2_prime_dvd9` with `e4_three9`).  Conditional on
`Check9Sound`, this is the per-prime contract of the nine-runner chain. -/
theorem e2_of_check9 (hsound : Check9Sound) (h7 : LRC7)
    (p : ℕ) (hp : p.Prime) (h11 : 11 < p)
    (X0 X1 X2 : Ctx) (h0 : TableOK9 X0 0 p) (h1 : TableOK9 X1 1 p) (h2 : TableOK9 X2 2 p)
    (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ) (Ct C1 C2 : ℕ → ℕ → ℕ)
    (a1 : checkTree0 X0 C0 H nx1 = true)
    (a2 : ∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true)
    (a3 : ∀ i, ∃ τ, τ < nT ∧ H i = H τ)
    (a4 : ∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) (a5 : ∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k)
    (a6 : ∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true)
    (a7 : ∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true)
    (v : Fin 8 → ℤ) (hce : IsCE9 v) : ∃ i, (p : ℤ) ∣ v i :=
  e2_prime_dvd9 p h11 (hsound p hp h11 X0 X1 X2 h0 h1 h2 C0 H nx1 nx2 nT n1 n2 Ct C1 C2
      a1 a2 a3 a4 a5 a6 a7) v hce.1 (e4_three9 h7 v hce) hce.2.2

end LRSpectrumFull.NineSound
