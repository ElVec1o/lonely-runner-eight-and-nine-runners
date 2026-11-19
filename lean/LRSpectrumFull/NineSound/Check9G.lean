/-
# Nine runners, soundness part 5b: `Check9SoundGb`, the checker soundness theorem, from `hier_good9`

`Check9SoundGb` is `Check9SoundG` (generator-faithful tables) with the extra hypothesis `p < 7000`.  The bound is needed:
the generated contexts store counters in 16-bit fields and the soundness proof uses `X.W < 2^15` (`hier_good9`), i.e.
`9p/2 < 32768`; for all the primes of the campaign (at most 241) it holds with a wide margin.  The unbounded
statement `Check9SoundG` is NOT derived here (and is not what the campaign needs).

`check9SoundGb` : a failing `lemma7Check 8 p` gives `V` with `Good9 p V` (`exists_good_of_not_check`), and `hier_good9`
refutes any accepted hierarchical certificate for a prime that has such a `V`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Assembly4
import LRSpectrumFull.NineSound.Norm9

namespace LRSpectrumFull.NineSound

open LRSpectrumFull LRSpectrumFull.NineProbe

def Check9SoundGb : Prop :=
  ∀ (p : ℕ), p.Prime → 11 < p → p < 7000 →
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

theorem check9SoundGb : Check9SoundGb := by
  intro p hp h11 hlt X0 X1 X2 hT0 hT1 hT2 C0 H nx1 nx2 nT n1 n2 Ct C1 C2 a1 a2 a3 a4 a5 a6 a7
  by_contra hne
  obtain ⟨V, hV⟩ := exists_good_of_not_check hp h11 hne
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have e0 : X0.W = p / 2 := by rw [hT0.2.1]; simp [lvlMult]
  have e1 : X1.W = 3 * p / 2 := by rw [hT1.2.1]; simp [lvlMult]
  have e2 : X2.W = 9 * p / 2 := by rw [hT2.2.1]; simp [lvlMult]
  exact hier_good9 (by omega) hp2 hV hT0 hT1 hT2 (by omega) (by omega) (by omega) (by omega)
    C0 H nx1 nx2 nT n1 n2 Ct C1 C2 a1 a2 a3 a4 a5 a6 a7

/-- the per-prime contract of the nine-runner chain, with the checker soundness PROVED (no `Check9Sound` hypothesis);
conditional only on `LRC7` and on the table statements of the generated contexts -/
theorem e2_prime_dvd9_of_tables (h7 : LRC7)
    (p : ℕ) (hp : p.Prime) (h11 : 11 < p) (hlt : p < 7000)
    (X0 X1 X2 : Ctx) (h0 : TableOK9g X0 0 p) (h1 : TableOK9g X1 1 p) (h2 : TableOK9g X2 2 p)
    (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ) (Ct C1 C2 : ℕ → ℕ → ℕ)
    (a1 : checkTree0 X0 C0 H nx1 = true)
    (a2 : ∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true)
    (a3 : ∀ i, ∃ τ, τ < nT ∧ H i = H τ)
    (a4 : ∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) (a5 : ∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k)
    (a6 : ∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true)
    (a7 : ∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true)
    (v : Fin 8 → ℤ) (hce : IsCE9 v) : ∃ i, (p : ℤ) ∣ v i :=
  e2_prime_dvd9 p h11 (check9SoundGb p hp h11 hlt X0 X1 X2 h0 h1 h2 C0 H nx1 nx2 nT n1 n2 Ct C1 C2
      a1 a2 a3 a4 a5 a6 a7) v hce.1 (e4_three9 h7 v hce) hce.2.2

end LRSpectrumFull.NineSound
