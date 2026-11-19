/-
# Nine runners, part 8: from the generated per-prime modules to `PrimeData p`

The generated modules of a prime prove, by `decide +kernel`, one Boolean statement per chunk
(`allTasks X0 TL nx1 lo n = true`, `allRoots X1 S1 nx2 D1 lo n = true`, ...), the top tree `checkTree0 ...`, and the
table statements `TableOK9g`.  This file turns them into `PrimeData p`:

* `gtab_surj`            `gtab L i = gtab L τ` for some `τ < L.length` (clauses a3, a4, a5);
* `allTasks_spec`, `tasks_step`, `allRoots_spec`, `roots_step`  chunk statements chain into the cumulative
                         statements `TasksUpTo`, `RootsUpTo` (clauses a2, a6, a7);
* `primeData_of_parts`   the assembly.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Plan9Glue
import LRSpectrumFull.NineProbe.Drv

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound LRSpectrumFull.NineProbe

theorem gtab_surj {α : Type} [Inhabited α] (L : List α) (hL : 0 < L.length) (i : ℕ) :
    ∃ τ, τ < L.length ∧ gtab L i = gtab L τ := by
  by_cases h : i < L.length
  · exact ⟨i, h, rfl⟩
  · refine ⟨0, hL, ?_⟩
    have h1 : gtab L i = L.headD default := by
      unfold gtab
      exact List.getD_eq_default _ _ (by omega)
    have h2 : gtab L 0 = L.headD default := by
      cases L with
      | nil => simp at hL
      | cons a t => simp [gtab]
    rw [h1, h2]

/-- every task below `n` is accepted -/
def TasksUpTo (X : Ctx) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ) (H : ℕ → St) (nx : ℕ → ℕ × ℕ × ℕ)
    (n : ℕ) : Prop :=
  ∀ τ, τ < n → checkTask X (tkC CH st nT τ) nx (H τ) = true

/-- every tree below `n` is accepted -/
def RootsUpTo (X : Ctx) (L : List (List ℕ)) (nx : ℕ → ℕ × ℕ × ℕ) (D : List (ℕ × ℕ × ℕ)) (n : ℕ) : Prop :=
  ∀ k, k < n → checkRootN X (ctOf L k) nx (gtab D k) = true

theorem tasks_base (X : Ctx) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ) (H : ℕ → St) (nx : ℕ → ℕ × ℕ × ℕ) :
    TasksUpTo X CH st nT H nx 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem roots_base (X : Ctx) (L : List (List ℕ)) (nx : ℕ → ℕ × ℕ × ℕ) (D : List (ℕ × ℕ × ℕ)) :
    RootsUpTo X L nx D 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem allTasks_spec (X : Ctx) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ) (H : ℕ → St) (nx : ℕ → ℕ × ℕ × ℕ) :
    ∀ n k, allTasks X CH st nT H nx k n = true → ∀ τ, k ≤ τ → τ < k + n →
      checkTask X (tkC CH st nT τ) nx (H τ) = true := by
  intro n
  induction n with
  | zero => intro k _ τ h1 h2; omega
  | succ n ih =>
    intro k h τ h1 h2
    simp only [allTasks, Bool.and_eq_true] at h
    by_cases hk : τ = k
    · subst hk; exact h.1
    · exact ih (k + 1) h.2 τ (by omega) (by omega)

theorem allRoots_spec (X : Ctx) (L : List (List ℕ)) (nx : ℕ → ℕ × ℕ × ℕ) (D : List (ℕ × ℕ × ℕ)) :
    ∀ n k, allRoots X L nx D k n = true → ∀ τ, k ≤ τ → τ < k + n →
      checkRootN X (ctOf L τ) nx (gtab D τ) = true := by
  intro n
  induction n with
  | zero => intro k _ τ h1 h2; omega
  | succ n ih =>
    intro k h τ h1 h2
    simp only [allRoots, Bool.and_eq_true] at h
    by_cases hk : τ = k
    · subst hk; exact h.1
    · exact ih (k + 1) h.2 τ (by omega) (by omega)

theorem tasks_step {X : Ctx} {CH : List (List (St × List ℕ))} {st : List ℕ} {nT : ℕ} {H : ℕ → St} {nx : ℕ → ℕ × ℕ × ℕ}
    {k n m : ℕ} (h : TasksUpTo X CH st nT H nx k) (hc : allTasks X CH st nT H nx k n = true) (hm : m = k + n) :
    TasksUpTo X CH st nT H nx m := by
  intro τ hτ
  by_cases hk : τ < k
  · exact h τ hk
  · exact allTasks_spec X CH st nT H nx n k hc τ (by omega) (by omega)

theorem roots_step {X : Ctx} {L : List (List ℕ)} {nx : ℕ → ℕ × ℕ × ℕ} {D : List (ℕ × ℕ × ℕ)} {k n m : ℕ}
    (h : RootsUpTo X L nx D k) (hc : allRoots X L nx D k n = true) (hm : m = k + n) :
    RootsUpTo X L nx D m := by
  intro τ hτ
  by_cases hk : τ < k
  · exact h τ hk
  · exact allRoots_spec X L nx D n k hc τ (by omega) (by omega)

/-- **The assembly of one prime.**  Generated data: contexts `X0 X1 X2`, the top stream `C0`, the task list `TL`
(delegated states with their streams), the descriptor lists `D1` (level-1 trees) and `D2` (level-2 trees), the
streams `L1`, `L2` of those trees.  Hypotheses: the three table statements, the top tree, and the cumulative
chunk statements.  Conclusion: `PrimeData p`. -/
theorem primeData_of_parts (p : ℕ) (X0 X1 X2 : Ctx) (C0 : ℕ → ℕ) (CH : List (List (St × List ℕ))) (st : List ℕ) (nT : ℕ) (HS : List St)
    (D1 D2 : List (ℕ × ℕ × ℕ)) (L1 L2 : List (List ℕ))
    (hTL : 0 < nT) (hHS : HS.length = nT) (hD1 : 0 < D1.length) (hD2 : 0 < D2.length)
    (h0 : TableOK9g X0 0 p) (h1 : TableOK9g X1 1 p) (h2 : TableOK9g X2 2 p)
    (htop : checkTree0 X0 C0 (gtab HS) (gtab D1) = true)
    (ht : TasksUpTo X0 CH st nT (gtab HS) (gtab D1) nT)
    (h6 : RootsUpTo X1 L1 (gtab D2) D1 D1.length)
    (h7 : RootsUpTo X2 L2 (fun _ => (0, 0, 0)) D2 D2.length) : PrimeData p := by
  refine ⟨X0, X1, X2, C0, gtab HS, gtab D1, gtab D2, nT, D1.length, D2.length,
    tkC CH st nT, ctOf L1, ctOf L2, h0, h1, h2, htop, ht, ?_, ?_, ?_, h6, h7⟩
  · intro i
    obtain ⟨τ, hτ, h⟩ := gtab_surj HS (by omega) i
    exact ⟨τ, by omega, h⟩
  · intro i
    exact gtab_surj D1 hD1 i
  · intro i
    exact gtab_surj D2 hD2 i

end LRSpectrumFull.NineSound.Plan9
