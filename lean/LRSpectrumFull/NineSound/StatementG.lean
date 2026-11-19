/-
# Nine runners, soundness part 2d: `TableOK9g`, the table statement matching the generator

Validating the real tables (part 2, `Tab13.lean`) showed three clauses of `Statement.TableOK9` that the
generator `gen_probe.rs` does NOT satisfy, so that `Check9Sound` as stated in part 1 does not apply to the
emitted contexts:

* `cbJ j` (the coverer mask of the time `j`) lists ALL classes of the window `[1, M/2]` that cover `j`,
  including the multiples of `p` (which `adm` excludes), not only the admissible ones;
* `m3` (the multiples of 3) lists all multiples of 3 of the window, again including multiples of `p`
  (for `M = 9p` the class `3p`).

`lowT` lists the classes `<= (3p-1)/2` of the window only (at level 0 the window is smaller).

The differences are harmless for soundness (every use of `cbJ` and `m3` is intersected with a mask contained
in `adm`), but the statement must say what the data is.  `TableOK9g` is `TableOK9` with these two clauses
corrected; `Check9SoundG` is `Check9Sound` with `TableOK9g`; `e2_of_check9g` is the same glue.  The part-1
module `Statement.lean` is left untouched.  No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Statement

namespace LRSpectrumFull.NineSound

open LRSpectrumFull LRSpectrumFull.NineProbe

/-- the generated context `X` of level `i` at the prime `p` (matching the generator exactly) -/
def TableOK9g (X : Ctx) (i p : ℕ) : Prop :=
  X.lvl = i ∧ X.W = (lvlMult i * p) / 2 ∧
  X.full = EightV4.compactOf (Win (lvlMult i * p)) ∧
  X.adm = EightV4.spreadOf (AdmC (lvlMult i * p) p) ∧
  X.m3 = (if i = 0 then 0
      else EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => x % 3 = 0))) ∧
  X.ones = EightV4.spreadOf (Finset.range (X.W + 1)) ∧
  X.lowp = EightV4.spreadOf (Finset.Icc 1 ((p - 1) / 2)) ∧
  X.lowT = EightV4.spreadOf (Finset.Icc 1 (min ((lvlMult i * p) / 2) ((3 * p - 1) / 2))) ∧
  (∀ x ∈ AdmC (lvlMult i * p) p, X.row (2 ^ (16 * x)) =
      (x, EightV4.compactOf ((Win (lvlMult i * p)).filter (fun j => covM (lvlMult i * p) j x)),
        (if 1 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM p x y)) else 0),
        (if 2 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM (3 * p) x y))
          else 0))) ∧
  (∀ j ∈ Win (lvlMult i * p), X.cbJ j =
      EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => covM (lvlMult i * p) j x))) ∧
  (∀ u acc, (∀ j, u.testBit j = true → j ∈ Win (lvlMult i * p)) →
    X.cntF u acc = acc + ∑ j ∈ (Win (lvlMult i * p)).filter (fun j => u.testBit j = true), X.cbJ j)

/-- `Check9Sound` stated with the generator-faithful table clause -/
def Check9SoundG : Prop :=
  ∀ (p : ℕ), p.Prime → 11 < p →
  ∀ (X0 X1 X2 : Ctx), TableOK9g X0 0 p → TableOK9g X1 1 p → TableOK9g X2 2 p →
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

theorem e2_of_check9g (hsound : Check9SoundG) (h7 : LRC7)
    (p : ℕ) (hp : p.Prime) (h11 : 11 < p)
    (X0 X1 X2 : Ctx) (h0 : TableOK9g X0 0 p) (h1 : TableOK9g X1 1 p) (h2 : TableOK9g X2 2 p)
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
