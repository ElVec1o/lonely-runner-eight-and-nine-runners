/-
# Nine runners, part 13: from table-valued chunk statements to `PrimeData p`

Companion of `DrvSound.lean` for the generator `gen_prime12`: the level-1 and level-2 tables are logarithmic-depth
functions (`NineProbe/DrvF.lean`) instead of lists.  `DrvSound.lean` is not edited; `tasks_step`, `gtab_surj`
and `TasksUpTo` are used as they stand (they are stated for an arbitrary descriptor function).

* `clampT_surj`           a clamped table takes only values `T k` with `k < N` (clauses a4, a5);
* `RootsUpToF`, `allRootsF_spec`, `rootsF_step`   chunk statements chain into the cumulative statement (clauses a6, a7);
* `primeData_of_partsF`   the assembly: same conclusion `PrimeData p` as `primeData_of_parts`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.DrvSound
import LRSpectrumFull.NineProbe.DrvF

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound LRSpectrumFull.NineProbe

theorem clampT_surj {α : Type} (T : ℕ → α) (N : ℕ) (hN : 0 < N) (i : ℕ) :
    ∃ k, k < N ∧ clampT T N i = clampT T N k := by
  by_cases h : i ≤ N - 1
  · refine ⟨i, by omega, rfl⟩
  · refine ⟨N - 1, by omega, ?_⟩
    have h1 : Nat.ble i (N - 1) = false := by
      cases hb : Nat.ble i (N - 1)
      · rfl
      · exact absurd (Nat.ble_eq.mp hb) h
    have h2 : Nat.ble (N - 1) (N - 1) = true := Nat.ble_eq.mpr (Nat.le_refl _)
    simp only [clampT, h1, h2, Nat.sub_eq, cond_false, cond_true]

/-- every tree below `n` is accepted (function-valued tables) -/
def RootsUpToF (X : Ctx) (CT : ℕ → ℕ → ℕ) (nx : ℕ → ℕ × ℕ × ℕ) (Dk : ℕ → ℕ × ℕ × ℕ) (n : ℕ) : Prop :=
  ∀ k, k < n → checkRootN X (CT k) nx (Dk k) = true

theorem rootsF_base (X : Ctx) (CT : ℕ → ℕ → ℕ) (nx : ℕ → ℕ × ℕ × ℕ) (Dk : ℕ → ℕ × ℕ × ℕ) :
    RootsUpToF X CT nx Dk 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem allRootsF_spec (X : Ctx) (CT : ℕ → ℕ → ℕ) (nx : ℕ → ℕ × ℕ × ℕ) (Dk : ℕ → ℕ × ℕ × ℕ) :
    ∀ n k, allRootsF X CT nx Dk k n = true → ∀ τ, k ≤ τ → τ < k + n →
      checkRootN X (CT τ) nx (Dk τ) = true := by
  intro n
  induction n with
  | zero => intro k _ τ h1 h2; omega
  | succ n ih =>
    intro k h τ h1 h2
    simp only [allRootsF, Bool.and_eq_true] at h
    by_cases hk : τ = k
    · subst hk; exact h.1
    · exact ih (k + 1) h.2 τ (by omega) (by omega)

theorem rootsF_step {X : Ctx} {CT : ℕ → ℕ → ℕ} {nx : ℕ → ℕ × ℕ × ℕ} {Dk : ℕ → ℕ × ℕ × ℕ} {k n m : ℕ}
    (h : RootsUpToF X CT nx Dk k) (hc : allRootsF X CT nx Dk k n = true) (hm : m = k + n) :
    RootsUpToF X CT nx Dk m := by
  intro τ hτ
  by_cases hk : τ < k
  · exact h τ hk
  · exact allRootsF_spec X CT nx Dk n k hc τ (by omega) (by omega)

/-- **The assembly of one prime, table-valued form.**  Same hypotheses as `primeData_of_parts` except that the
descriptor tables `T1`, `T2` (level 1 and 2) and the stream tables `S1`, `S2` are functions with a stated size
`N1`, `N2` (`clampT`), not lists.  Conclusion: `PrimeData p`. -/
theorem primeData_of_partsF (p : ℕ) (X0 X1 X2 : Ctx) (C0 : ℕ → ℕ) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ)
    (HS : List St) (T1 T2 : ℕ → ℕ × ℕ × ℕ) (N1 N2 : ℕ) (S1 S2 : ℕ → List ℕ)
    (hTL : 0 < nT) (hHS : HS.length = nT) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (h0 : TableOK9g X0 0 p) (h1 : TableOK9g X1 1 p) (h2 : TableOK9g X2 2 p)
    (htop : checkTree0 X0 C0 (gtab HS) (clampT T1 N1) = true)
    (ht : TasksUpTo X0 CH st nT (gtab HS) (clampT T1 N1) nT)
    (h6 : RootsUpToF X1 (ctT S1 N1) (clampT T2 N2) (clampT T1 N1) N1)
    (h7 : RootsUpToF X2 (ctT S2 N2) (fun _ => (0, 0, 0)) (clampT T2 N2) N2) : PrimeData p := by
  refine ⟨X0, X1, X2, C0, gtab HS, clampT T1 N1, clampT T2 N2, nT, N1, N2,
    tkC CH st nT, ctT S1 N1, ctT S2 N2, h0, h1, h2, htop, ht, ?_, ?_, ?_, h6, h7⟩
  · intro i
    obtain ⟨τ, hτ, h⟩ := gtab_surj HS (by omega) i
    exact ⟨τ, by omega, h⟩
  · intro i
    exact clampT_surj T1 N1 hN1 i
  · intro i
    exact clampT_surj T2 N2 hN2 i

end LRSpectrumFull.NineSound.Plan9
