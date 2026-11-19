/-
# Nine runners, part 7c: the final assembly shape, with `PrimeData` as the explicit per-prime hypothesis

`PrimeData p` is the data of one prime of the campaign, exactly the hypotheses of `e2_prime_dvd9_of_tables`: three
generated contexts satisfying `TableOK9g` (levels 0, 1, 2 at `p`, `3p`, `9p`), the level-0 certificate with its
delegation table, the delegated subtree certificates, the level-1 and level-2 tree certificates with their
descriptor tables, and the seven acceptance clauses `a1` to `a7`.  `PrimeData p` is an `exists`: the campaign proves
it by exhibiting the generated data and kernel-checking the clauses (table validation and replay are separate parts).

`nine_runners_of_data` is the final assembly: `LRC7` and `PrimeData p` for every `p` in `S36` give `1/9 <= ML v` for
every positive `v : Fin 8 -> Int`.  These two are the ONLY hypotheses.  `PrimeData` is not vacuous: it fails at
`p = 13` (`Ctl8.ctl_primeData_13_false`), because `check9SoundGb` makes any accepted certificate imply
`lemma7Check 8 p = true` and `lemma7Check 8 13 = true` is false.

No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Check9G
import LRSpectrumFull.NineSound.Plan9

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound LRSpectrumFull.NineProbe

/-- the data of one prime: the hypotheses of `e2_prime_dvd9_of_tables` bundled as an `exists` -/
def PrimeData (p : ℕ) : Prop :=
  ∃ (X0 X1 X2 : Ctx) (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → ℕ × ℕ × ℕ) (nT n1 n2 : ℕ)
    (Ct C1 C2 : ℕ → ℕ → ℕ),
    TableOK9g X0 0 p ∧ TableOK9g X1 1 p ∧ TableOK9g X2 2 p ∧
    checkTree0 X0 C0 H nx1 = true ∧
    (∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true) ∧
    (∀ i, ∃ τ, τ < nT ∧ H i = H τ) ∧
    (∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) ∧
    (∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k) ∧
    (∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true) ∧
    (∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true)

/-- the per-prime divisibility fact from the per-prime data -/
theorem dvd_of_primeData (h7 : LRC7) (p : ℕ) (hp : p.Prime) (h11 : 11 < p) (hlt : p < 7000)
    (hd : PrimeData p) (w : Fin 8 → ℤ) (hce : IsCE9 w) : ∃ i, (p : ℤ) ∣ w i := by
  obtain ⟨X0, X1, X2, C0, H, nx1, nx2, nT, n1, n2, Ct, C1, C2, h0, h1, h2, a1, a2, a3, a4, a5, a6, a7⟩ := hd
  exact e2_prime_dvd9_of_tables h7 p hp h11 hlt X0 X1 X2 h0 h1 h2 C0 H nx1 nx2 nT n1 n2 Ct C1 C2
    a1 a2 a3 a4 a5 a6 a7 w hce

/-- every prime of `S36` is prime, above 11 and below 7000 (the range of `check9SoundGb`) -/
theorem S36_ok : ∀ p ∈ S36, p.Prime ∧ 11 < p ∧ p < 7000 := by
  intro p hp
  have h := mem_S36.mp hp
  simp only [S36L, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The final assembly shape (nine runners).**  Hypotheses: `LRC7` and `PrimeData p` for each `p` in `S36`. -/
theorem nine_runners_of_data (h7 : LRC7) (hd : ∀ p ∈ S36, PrimeData p)
    (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 9 ≤ ML v :=
  nine_runners_of h7
    (fun p hp w hce => dvd_of_primeData h7 p (S36_ok p hp).1 (S36_ok p hp).2.1 (S36_ok p hp).2.2
      (hd p hp) w hce) v hv

end LRSpectrumFull.NineSound.Plan9
