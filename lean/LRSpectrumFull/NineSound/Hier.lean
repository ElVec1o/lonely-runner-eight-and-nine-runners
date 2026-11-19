/-
# Nine runners, soundness part 2b: the hierarchy core (slot accounting and completeness of a path)

`Check9Sound` (Statement.lean) quantifies over the whole certificate of one prime: the level-0 tree
`C0` (moduli `p`) with its delegated subtrees `H`, `Ct`, the level-1 trees `C1` (modulus `3p`, one per
descriptor `nx1 k`) and the level-2 trees `C2` (modulus `9p`, one per descriptor `nx2 k`).

This file proves the ASSEMBLY half of that theorem, for the checker as written and abstractly in the
semantic predicates `Cmp0, Cmp1, Cmp2` of the three levels (`Sem` of Replay.lean):

* `rootN_complete`   a level `>= 1` tree `checkRootN X C nx d` that is accepted, started from the root
                     state `rootSt X d` of a descriptor in `Cmp`, ends at a leaf `5 i` (descriptor test
                     `leafOK` passes) or the root is infeasible (`6 <` forced multiples of 3);
* `task_complete`    a delegated subtree `checkTask` likewise;
* `tree0_complete`   the top tree `checkTree0`: every path ends in a leaf `5 i` or in a delegation `7 i`;
* `hier_complete`    every index a leaf names is the descriptor of a tree that is itself checked
                     (`a4`, `a5`: at least once; "exactly once" is not needed for soundness), every
                     delegated state is one of the checked tasks (`a3`), level-2 trees have no leaf
                     (`leafOK` is false at `lvl = 2`), hence NO path survives: `Cmp0 (root0 X0)` is
                     impossible.

The statements `t01`, `t12` (a leaf state of level `i` in `Cmp` lifts its descriptor to a root state of
level `i + 1` in `Cmp`) are the slot accounting: they are what the part-4 math (distinct classes mod `p`
have disjoint preimages, items are served by distinct picks, `|items| + fr = 8`) must supply.  They are
hypotheses here.  No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Replay

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe

/-- a tree descriptor `(icm, ict, fr)`: items of the modulus `p` (spread), items of `3p` (spread),
free picks -/
abbrev Desc := ℕ × ℕ × ℕ

theorem leafOK_lvl2 (X : Ctx) (hX : X.lvl = 2) (nx : ℕ → Desc) (s : St) (i : ℕ) :
    leafOK X nx s i = false := by
  unfold leafOK
  rcases hnx : nx i with ⟨a, b, c⟩
  simp [hX, ltN]

theorem stEq_noH_false (s : St) (hr : s.r ≠ 99) (i : ℕ) : stEq (noH i) s = false := by
  unfold stEq noH
  simp only [Bool.and_eq_true, Nat.beq_eq]
  cases h : Nat.beq 99 s.r with
  | false => simp [h]
  | true => exact absurd (Nat.eq_of_beq_eq_true h).symm hr

/-- a delegated subtree from an explicit state (counters recomputed from `unc`) -/
theorem task_complete (X : Ctx) (Cmp : St → Prop) (hS : Sem X Cmp) (C : ℕ → ℕ) (nx : ℕ → Desc)
    (h : St) (hchk : checkTask X C nx h = true)
    (hc : Cmp { h with cu := X.cntF h.unc 0, nu := pcl 1024 h.unc 0 })
    (hr : ∀ s, Cmp s → ∀ i, stEq (noH i) s = false) :
    ∃ s' i, Cmp s' ∧ leafOK X nx s' i = true := by
  unfold checkTask isSome at hchk
  rcases hgo : go X C noH nx 12 { h with cu := X.cntF h.unc 0, nu := pcl 1024 h.unc 0 } 0 with _ | pos
  · rw [hgo] at hchk; simp at hchk
  · obtain ⟨s', i, hs', hleaf | hstE⟩ := go_complete X noH nx Cmp hS C 12 _ 0 pos hgo hc
    · exact ⟨s', i, hs', hleaf⟩
    · rw [hr s' hs' i] at hstE; simp at hstE

/-- the top tree: every path ends in a leaf `5 i` or in a delegation `7 i` -/
theorem tree0_complete (X : Ctx) (Cmp : St → Prop) (hS : Sem X Cmp) (C : ℕ → ℕ) (H : ℕ → St)
    (nx : ℕ → Desc) (hchk : checkTree0 X C H nx = true) (hc : Cmp (root0 X)) :
    ∃ s' i, Cmp s' ∧ (leafOK X nx s' i = true ∨ stEq (H i) s' = true) := by
  unfold checkTree0 isSome at hchk
  rcases hgo : go X C H nx 12 (root0 X) 0 with _ | pos
  · rw [hgo] at hchk; simp at hchk
  · exact go_complete X H nx Cmp hS C 12 _ 0 pos hgo hc

/-- a tree at level `>= 1` from its descriptor -/
theorem rootN_complete (X : Ctx) (Cmp : St → Prop) (hS : Sem X Cmp) (C : ℕ → ℕ) (nx : ℕ → Desc)
    (d : Desc) (hchk : checkRootN X C nx d = true)
    (hc : Cmp (rootSt X d.1 d.2.1 d.2.2))
    (hinf : ltN 6 (spc X (Nat.land d.2.1 X.m3)) = true → False)
    (hr : ∀ s, Cmp s → ∀ i, stEq (noH i) s = false) :
    ∃ s' i, Cmp s' ∧ leafOK X nx s' i = true := by
  obtain ⟨icm, ict, fr⟩ := d
  unfold checkRootN at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨_, hb⟩ := hchk
  rcases hl : ltN 6 (spc X (Nat.land ict X.m3)) with _ | _
  · rw [hl] at hb
    simp only [cond_false, isSome] at hb
    rcases hgo : go X C noH nx 12 (rootSt X icm ict fr) 0 with _ | pos
    · rw [hgo] at hb; simp at hb
    · obtain ⟨s', i, hs', hleaf | hstE⟩ := go_complete X noH nx Cmp hS C 12 _ 0 pos hgo hc
      · exact ⟨s', i, hs', hleaf⟩
      · rw [hr s' hs' i] at hstE; simp at hstE
  · exact (hinf hl).elim

/-- **Completeness of the three-level certificate (assembly half of `Check9Sound`).**  Under the
hypotheses of `Check9Sound` (`a1`-`a7`, the same shapes), the semantic predicates of the levels
(`S0`-`S2`), the slot-accounting transitions `t01`, `t12` and the delegation transfer `hdel`, no state of
`Cmp0` survives from the root of the level-0 tree. -/
theorem hier_complete (X0 X1 X2 : Ctx) (Cmp0 Cmp1 Cmp2 : St → Prop)
    (S0 : Sem X0 Cmp0) (S1 : Sem X1 Cmp1) (S2 : Sem X2 Cmp2)
    (C0 : ℕ → ℕ) (H : ℕ → St) (nx1 nx2 : ℕ → Desc) (nT n1 n2 : ℕ) (Ct C1 C2 : ℕ → ℕ → ℕ)
    (a1 : checkTree0 X0 C0 H nx1 = true)
    (a2 : ∀ τ, τ < nT → checkTask X0 (Ct τ) nx1 (H τ) = true)
    (a3 : ∀ i, ∃ τ, τ < nT ∧ H i = H τ)
    (a4 : ∀ i, ∃ k, k < n1 ∧ nx1 i = nx1 k) (a5 : ∀ i, ∃ k, k < n2 ∧ nx2 i = nx2 k)
    (a6 : ∀ k, k < n1 → checkRootN X1 (C1 k) nx2 (nx1 k) = true)
    (a7 : ∀ k, k < n2 → checkRootN X2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) = true)
    (hlvl2 : X2.lvl = 2)
    (hroot : Cmp0 (root0 X0))
    (hdel : ∀ s h, Cmp0 s → stEq h s = true →
      Cmp0 { h with cu := X0.cntF h.unc 0, nu := pcl 1024 h.unc 0 })
    (hr0 : ∀ s, Cmp0 s → ∀ i, stEq (noH i) s = false)
    (hr1 : ∀ s, Cmp1 s → ∀ i, stEq (noH i) s = false)
    (hr2 : ∀ s, Cmp2 s → ∀ i, stEq (noH i) s = false)
    (t01 : ∀ s i, Cmp0 s → leafOK X0 nx1 s i = true →
      Cmp1 (rootSt X1 (nx1 i).1 (nx1 i).2.1 (nx1 i).2.2))
    (t12 : ∀ s i, Cmp1 s → leafOK X1 nx2 s i = true →
      Cmp2 (rootSt X2 (nx2 i).1 (nx2 i).2.1 (nx2 i).2.2))
    (inf1 : ∀ d : Desc, Cmp1 (rootSt X1 d.1 d.2.1 d.2.2) →
      ltN 6 (spc X1 (Nat.land d.2.1 X1.m3)) = true → False)
    (inf2 : ∀ d : Desc, Cmp2 (rootSt X2 d.1 d.2.1 d.2.2) →
      ltN 6 (spc X2 (Nat.land d.2.1 X2.m3)) = true → False) : False := by
  -- level 2: no leaf exists, so a tree of level 2 started in `Cmp2` is impossible
  have lvl2_false : ∀ i, Cmp2 (rootSt X2 (nx2 i).1 (nx2 i).2.1 (nx2 i).2.2) → False := by
    intro i hc
    obtain ⟨k, hk, hik⟩ := a5 i
    have hck := a7 k hk
    rw [hik] at hc
    obtain ⟨s', j, _, hleaf⟩ := rootN_complete X2 Cmp2 S2 (C2 k) (fun _ => (0, 0, 0)) (nx2 k) hck hc
      (fun hl => inf2 _ hc hl) hr2
    rw [leafOK_lvl2 X2 hlvl2] at hleaf; simp at hleaf
  -- level 1: a leaf of level 1 lifts to level 2
  have lvl1_false : ∀ i, Cmp1 (rootSt X1 (nx1 i).1 (nx1 i).2.1 (nx1 i).2.2) → False := by
    intro i hc
    obtain ⟨k, hk, hik⟩ := a4 i
    have hck := a6 k hk
    rw [hik] at hc
    obtain ⟨s', j, hs', hleaf⟩ := rootN_complete X1 Cmp1 S1 (C1 k) nx2 (nx1 k) hck hc
      (fun hl => inf1 _ hc hl) hr1
    exact lvl2_false j (t12 s' j hs' hleaf)
  -- level 0: a leaf lifts to level 1
  have leaf0_false : ∀ s i, Cmp0 s → leafOK X0 nx1 s i = true → False :=
    fun s i hs hl => lvl1_false i (t01 s i hs hl)
  obtain ⟨s', i, hs', hex⟩ := tree0_complete X0 Cmp0 S0 C0 H nx1 a1 hroot
  rcases hex with hl | hst
  · exact leaf0_false s' i hs' hl
  · obtain ⟨τ, hτ, hHτ⟩ := a3 i
    rw [hHτ] at hst
    obtain ⟨s'', j, hs'', hl⟩ := task_complete X0 Cmp0 S0 (Ct τ) nx1 (H τ) (a2 τ hτ)
      (hdel s' (H τ) hs' hst) hr0
    exact leaf0_false s'' j hs'' hl

end LRSpectrumFull.NineSound
