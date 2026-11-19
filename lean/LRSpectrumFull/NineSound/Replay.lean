/-
# Nine runners, soundness part 2a: path completeness of the replay (`kids`, `go` of `NineProbe.Check`)

The checker `go` replays a certificate tree.  This file proves, for the checker as written and for ANY
semantic predicate `Cmp` on node states that satisfies the three local obligations of `Sem`, that an
accepted replay accounts for every path from the node to a leaf:

* `Sem.bound`   a tag-3 record (`tailOK`) is never accepted on a state of `Cmp` (this is the content of
                `NineSound.boundLeaf_false` once the counter invariant is known);
* `Sem.nocov`   a tag-2 record: an uncovered time with no allowed coverer contradicts `Cmp`;
* `Sem.branch`  a tag-0 record: an uncovered time `j` has an allowed coverer `e` whose child state
                (with the sibling exclusion `avr` built by `kids`) is again in `Cmp`.

`kids_sound` is the loop lemma: the child of the `e`-th coverer receives exactly the available classes
minus the coverers `<= e`; `go_complete` is the induction over the fuel: an accepted replay from a state
in `Cmp` ends at a leaf record of tag 5 (descriptor test `leafOK` passes) or a delegation of tag 7
(`stEq (H i) s'`), with the final state again in `Cmp`.  No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineProbe.Check
import LRSpectrumFull.EightCheckSound

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe

theorem lowB_spec (m : ℕ) (hm : m ≠ 0) :
    ∃ k, lowB m = 2 ^ k ∧ m.testBit k = true ∧ ∀ i < k, m.testBit i = false :=
  EightV4.low_iso m hm

theorem beq_zero_false (m : ℕ) (hm : m ≠ 0) : Nat.beq m 0 = false := by
  cases m with
  | zero => exact absurd rfl hm
  | succ n => rfl

theorem testBit_clr_pow (x k i : ℕ) :
    (clr x (2 ^ k)).testBit i = (x.testBit i && !decide (k = i)) := by
  have h := EightV4.testBit_clr x (2 ^ k) i
  rw [Nat.testBit_two_pow] at h
  exact h

/-- **The `kids` loop.**  If every child replay that succeeds satisfies `Res`, then in an accepted
`kids` loop over the coverer mask `m`, the child of each coverer `e` of `m` was entered with the
available mask `avr` minus the coverers `k <= e` of `m` (sibling exclusion), and satisfies `Res`. -/
theorem kids_sound (X : Ctx) (g : St → ℕ → Option ℕ) (s : St) (Res : St → Prop)
    (hg : ∀ c pos pos', g c pos = some pos' → Res c) :
    ∀ (f m avr pos pos' : ℕ), kids X g s f m avr pos = some pos' →
      ∀ e, m.testBit e = true →
        ∃ avr', (∀ k, avr'.testBit k = (avr.testBit k && !(m.testBit k && decide (k ≤ e)))) ∧
          Res (childSt X s (2 ^ e) avr') := by
  intro f
  induction f with
  | zero => intro m avr pos pos' h; simp [kids] at h
  | succ f ih =>
    intro m avr pos pos' h e he
    by_cases hm0 : m = 0
    · subst hm0; simp at he
    · have hb : Nat.beq m 0 = false := beq_zero_false m hm0
      obtain ⟨k0, hk0, hk0t, hk0l⟩ := lowB_spec m hm0
      simp only [kids, hb, cond_false] at h
      rw [hk0] at h
      rcases hgm : g (childSt X s (2 ^ k0) (clr avr (2 ^ k0))) pos with _ | pos1
      · rw [hgm] at h; simp at h
      · rw [hgm] at h
        simp only at h
        by_cases hek : e = k0
        · subst hek
          refine ⟨clr avr (2 ^ e), ?_, hg _ _ _ hgm⟩
          intro k
          rw [testBit_clr_pow]
          by_cases hk : e = k
          · subst hk; simp [he]
          · have : ¬ (m.testBit k = true ∧ k ≤ e) := by
              rintro ⟨h1, h2⟩
              have : k < e := lt_of_le_of_ne h2 (Ne.symm hk)
              rw [hk0l k this] at h1; exact absurd h1 (by simp)
            simp only [hk, decide_false, Bool.not_false, Bool.and_true]
            by_cases h3 : m.testBit k = true
            · have : ¬ k ≤ e := fun h4 => this ⟨h3, h4⟩
              simp [h3, this]
            · simp [h3]
        · have he' : (clr m (2 ^ k0)).testBit e = true := by
            rw [testBit_clr_pow]; simp [he, Ne.symm hek]
          obtain ⟨avr'', hchar, hres⟩ := ih _ _ _ _ h e he'
          refine ⟨avr'', ?_, hres⟩
          have hle : k0 ≤ e := by
            by_contra hlt
            have := hk0l e (by omega)
            rw [this] at he; exact absurd he (by simp)
          intro k
          rw [hchar k, testBit_clr_pow, testBit_clr_pow]
          by_cases hk : k0 = k
          · subst hk; simp [hk0t, hle]
          · simp [hk]

/-- The local semantic obligations of an abstract compatibility predicate `Cmp` on node states of
level `X` (see the file header). -/
structure Sem (X : Ctx) (Cmp : St → Prop) : Prop where
  bound : ∀ (C : ℕ → ℕ) (s : St) (pos pos' : ℕ), Cmp s →
    tailOK X C s.cu s.nu (allowed X s) s.r pos = some pos' → False
  nocov : ∀ (s : St) (j : ℕ), Cmp s → bitC s.unc j = true →
    Nat.land (X.cbJ j) (allowed X s) = 0 → False
  branch : ∀ (s : St) (j : ℕ), Cmp s → bitC s.unc j = true →
    ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
      ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
          !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
        Cmp (childSt X s (2 ^ e) avr)

theorem nat_land_ne_zero_of_testBit (a b e : ℕ) (h : (Nat.land a b).testBit e = true) :
    Nat.land a b ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

/-- **Path completeness of an accepted replay.**  From a state in `Cmp`, an accepted `go` ends in a
leaf of tag 5 whose descriptor test passes, or in a delegation of tag 7, with `Cmp` still holding at
the exit state.  Bound-prune leaves (tag 3) and contradiction-by-covering leaves (tag 2) are excluded
by `Sem.bound` and `Sem.nocov`: they cannot be reached from a state of `Cmp`. -/
theorem go_complete (X : Ctx) (H : ℕ → St) (nx : ℕ → ℕ × ℕ × ℕ) (Cmp : St → Prop)
    (hS : Sem X Cmp) (C : ℕ → ℕ) :
    ∀ (f : ℕ) (s : St) (pos pos' : ℕ), go X C H nx f s pos = some pos' → Cmp s →
      ∃ s' i, Cmp s' ∧ (leafOK X nx s' i = true ∨ stEq (H i) s' = true) := by
  intro f
  induction f with
  | zero => intro s pos pos' h; simp [go] at h
  | succ f ih =>
    intro s pos pos' h hc
    simp only [go, EightV4.beq_eq_decide] at h
    by_cases h5 : rd C pos = 5
    · simp only [h5, decide_true, cond_true] at h
      rcases hl : leafOK X nx s (rd C (Nat.succ pos)) with _ | _
      · rw [hl] at h; simp at h
      · exact ⟨s, rd C (Nat.succ pos), hc, Or.inl hl⟩
    by_cases h7 : rd C pos = 7
    · simp only [h7, decide_true, cond_true, show (7 : ℕ) ≠ 5 by omega, decide_false, cond_false] at h
      rcases hl : stEq (H (rd C (Nat.succ pos))) s with _ | _
      · rw [hl] at h; simp at h
      · exact ⟨s, rd C (Nat.succ pos), hc, Or.inr hl⟩
    by_cases h0 : rd C pos = 0
    · simp only [h0, h5, h7, decide_true, cond_true, decide_false, cond_false, show (0 : ℕ) ≠ 5 by omega,
        show (0 : ℕ) ≠ 7 by omega] at h
      rcases hj : bitC s.unc (rd C (Nat.succ pos)) with _ | _
      · rw [hj] at h; simp at h
      · rw [hj] at h
        simp only [cond_true] at h
        obtain ⟨e, hme, hbr⟩ := hS.branch s (rd C (Nat.succ pos)) hc hj
        obtain ⟨avr, hchar, hres⟩ := kids_sound X (go X C H nx f) s
          (fun c => Cmp c → ∃ s' i, Cmp s' ∧ (leafOK X nx s' i = true ∨ stEq (H i) s' = true))
          (fun c pos pos' hg => ih c pos pos' hg) 1024 _ s.av _ pos' h e hme
        exact hres (hbr avr hchar)
    by_cases h2 : rd C pos = 2
    · simp only [h2, h5, h7, h0, decide_true, cond_true, decide_false, cond_false, show (2 : ℕ) ≠ 5 by omega,
        show (2 : ℕ) ≠ 7 by omega, show (2 : ℕ) ≠ 0 by omega] at h
      rcases hj : bitC s.unc (rd C (Nat.succ pos)) with _ | _
      · rw [hj] at h; simp at h
      · rw [hj] at h
        simp only [Bool.true_and] at h
        rcases hz : decide (Nat.land (X.cbJ (rd C (Nat.succ pos))) (allowed X s) = 0) with _ | _
        · rw [hz] at h; simp at h
        · exact absurd (of_decide_eq_true hz) (fun hz0 => hS.nocov s _ hc hj hz0)
    by_cases h3 : rd C pos = 3
    · simp only [h3, h5, h7, h0, h2, decide_true, cond_true, decide_false, cond_false,
        show (3 : ℕ) ≠ 5 by omega, show (3 : ℕ) ≠ 7 by omega, show (3 : ℕ) ≠ 0 by omega,
        show (3 : ℕ) ≠ 2 by omega] at h
      exact (hS.bound C s _ _ hc h).elim
    · simp only [h5, h7, h0, h2, h3, decide_false, cond_false] at h
      simp at h

end LRSpectrumFull.NineSound
