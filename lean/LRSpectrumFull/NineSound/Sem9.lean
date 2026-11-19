/-
# Nine runners, soundness part 3a: the counter invariant and the generic semantics (`Sem.bound`, `Sem.nocov`)

`Replay.lean` reduces the path completeness of the replay to three local obligations `Sem` on a semantic
predicate `Cmp`.  This file discharges the two that concern the pruning records, for ANY predicate `Cmp`
that implies

* `WF X M s`    the counter invariant of the node state `s` of the level with window `Win M`:
                the uncovered times are inside the window, `cu` is the exact spread sum of the per class
                counts `|{uncovered j covered by v}|`, and `nu <= |uncovered|`;
* `Compl X M s` a COMPLETION exists: a set `Z` of at most `r` classes, all allowed by `allowed X s`, that
                covers every uncovered time (the semantic notion of a good class set).

`sem_bound_of` (a tag-3 record is never accepted: E8 `uniform_bound_no_cover` through
`boundLeaf_false`), `sem_nocov_of` (a tag-2 record is never accepted), and `sem_mk` (a `Sem` from the
two plus the branch obligation).  `wf_child` is the counter invariant of the child update `childSt`
(`child_state9`, counter half): the exact `cu`, `nu` bookkeeping is preserved by taking a class `c`.
`wf_of_unc` gives the invariant for the root states (`rootSt`, `root0`, delegated tasks).
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Masks

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

theorem testBit_land9 (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_land a b i

theorem bitC_eq9 (x j : ℕ) : bitC x j = x.testBit j := EightV4.bitC_eq x j

/-- `v` is a class of the window of `M` covering the time `j` -/
def cvr (M j v : ℕ) : Prop := v ∈ Win M ∧ covM M j v

instance (M j v : ℕ) : Decidable (cvr M j v) := by unfold cvr; infer_instance

/-- the uncovered times of a state -/
def uncS (M : ℕ) (s : St) : Finset ℕ := (Win M).filter (fun j => s.unc.testBit j = true)

/-- the counter invariant -/
structure WF (X : Ctx) (M : ℕ) (s : St) : Prop where
  unc : ∀ j, s.unc.testBit j = true → j ∈ Win M
  cu : s.cu = ∑ v ∈ range (X.W + 1), ((uncS M s).filter (fun j => cvr M j v)).card * 2 ^ (16 * v)
  nu : s.nu ≤ (uncS M s).card

/-- a completion of a state: at most `r` allowed classes covering all uncovered times -/
def Compl (X : Ctx) (M : ℕ) (s : St) : Prop :=
  ∃ Z : Finset ℕ, (∀ v ∈ Z, v ∈ Win M ∧ bitS (allowed X s) v = true) ∧ Z.card ≤ s.r ∧
    ∀ j ∈ uncS M s, ∃ v ∈ Z, covM M j v

theorem win_lt {M v : ℕ} (h : v ∈ Win M) : v < M / 2 + 1 := by
  simp only [Win, mem_Icc] at h; omega

/-- the coverer mask of `j` has the bit `16 v` iff `v` covers `j` -/
theorem cb_bit {X : Ctx} {i p : ℕ} (hT : TableOK9g X i p) {j : ℕ} (hj : j ∈ Win (lvlMult i * p)) (v : ℕ) :
    (X.cbJ j).testBit (16 * v) = decide (cvr (lvlMult i * p) j v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcb, _⟩ := hT
  rw [hcb j hj, tb_sp]
  exact decide_eq_decide.mpr (by simp [cvr, mem_filter])

/-- **The counter sum** of a set of times `u` inside the window. -/
theorem cntF_spec (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (u : ℕ)
    (hu : ∀ j, u.testBit j = true → j ∈ Win (lvlMult i * p)) :
    X.cntF u 0 = ∑ v ∈ range (X.W + 1),
      (((Win (lvlMult i * p)).filter (fun j => u.testBit j = true)).filter
        (fun j => cvr (lvlMult i * p) j v)).card * 2 ^ (16 * v) := by
  obtain ⟨_, hWd, _, _, _, _, _, _, _, hcb, hcnt⟩ := hT
  rw [hcnt u 0 hu, zero_add]
  set N := (Win (lvlMult i * p)).filter (fun j => u.testBit j = true) with hN
  have e1 : ∑ j ∈ N, X.cbJ j = ∑ j ∈ N, (fun _ => 1) j *
      EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => covM (lvlMult i * p) j x)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [one_mul, hcb j (mem_filter.mp hj).1]
  rw [e1, EightV4.sum_spread N (fun _ => 1)
    (fun j => (Win (lvlMult i * p)).filter (fun x => covM (lvlMult i * p) j x)) (X.W + 1) ?_]
  · apply Finset.sum_congr rfl
    intro v _
    congr 1
    rw [Finset.sum_boole, Nat.cast_id]
    apply congrArg
    apply Finset.filter_congr
    intro j _
    simp [cvr, mem_filter]
  · intro j _ v hv
    have := win_lt (mem_filter.mp hv).1
    omega

theorem uncS_card_lt (X : Ctx) (M : ℕ) (hW : X.W = M / 2) (hW15 : X.W < 2 ^ 15) (s : St) :
    (uncS M s).card < 2 ^ 15 := by
  have h1 : (uncS M s).card ≤ (Win M).card := Finset.card_le_card (Finset.filter_subset _ _)
  simp only [Win, Nat.card_Icc] at h1
  omega

/-- **`Sem.bound`, generically.**  A tag-3 record is never accepted on a state with the counter
invariant and a completion. -/
theorem sem_bound_of (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (hW15 : X.W < 2 ^ 15)
    (s : St) (hwf : WF X (lvlMult i * p) s) (hc : Compl X (lvlMult i * p) s)
    (C : ℕ → ℕ) (pos pos' : ℕ) (h : tailOK X C s.cu s.nu (allowed X s) s.r pos = some pos') : False := by
  have hT' := hT
  obtain ⟨Z, hZ, hZr, hZc⟩ := hc
  obtain ⟨_, hWd, _, _, _, hones, _⟩ := hT'
  have hones' : X.ones = ∑ v ∈ range (X.W + 1), 1 * 2 ^ (16 * v) := by
    rw [hones]; simp [EightV4.spreadOf]
  refine boundLeaf_false X C (cvr (lvlMult i * p)) (uncS (lvlMult i * p) s)
    (uncS_card_lt X _ hWd hW15 s) ?_ hones' s.cu s.nu (allowed X s) s.r pos pos' hwf.cu hwf.nu h Z ?_
    (fun v hv => (hZ v hv).2) hZr ?_
  · intro j v hv
    have := win_lt hv.1; omega
  · intro v hv
    have := win_lt (hZ v hv).1; omega
  · intro j hj
    obtain ⟨v, hv, hcv⟩ := hZc j hj
    exact ⟨v, hv, (hZ v hv).1, hcv⟩

/-- **`Sem.nocov`, generically.**  An uncovered time without allowed coverer contradicts a completion. -/
theorem sem_nocov_of (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p)
    (s : St) (hwf : WF X (lvlMult i * p) s) (hc : Compl X (lvlMult i * p) s) (j : ℕ)
    (hj : bitC s.unc j = true) (h0 : Nat.land (X.cbJ j) (allowed X s) = 0) : False := by
  rw [bitC_eq9] at hj
  have hjW := hwf.unc j hj
  obtain ⟨Z, hZ, _, hZc⟩ := hc
  obtain ⟨v, hv, hcv⟩ := hZc j (mem_filter.mpr ⟨hjW, hj⟩)
  have h1 : (X.cbJ j).testBit (16 * v) = true := by
    rw [cb_bit hT hjW]; exact decide_eq_true ⟨(hZ v hv).1, hcv⟩
  have h2 := (hZ v hv).2
  have h3 : (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * v) = true := by
    rw [testBit_land9, h1]; exact h2
  rw [h0] at h3; simp at h3

/-- A `Sem` from the generic part and the branch obligation. -/
theorem sem_mk (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (hW15 : X.W < 2 ^ 15) (Cmp : St → Prop)
    (hG : ∀ s, Cmp s → WF X (lvlMult i * p) s ∧ Compl X (lvlMult i * p) s)
    (hbr : ∀ (s : St) (j : ℕ), Cmp s → bitC s.unc j = true →
      ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
        ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
          !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
          Cmp (childSt X s (2 ^ e) avr)) : Sem X Cmp where
  bound := fun C s pos pos' hs h => sem_bound_of X i p hT hW15 s (hG s hs).1 (hG s hs).2 C pos pos' h
  nocov := fun s j hs hj h0 => sem_nocov_of X i p hT s (hG s hs).1 (hG s hs).2 j hj h0
  branch := hbr

/-! ## The counter invariant of the child update -/

theorem childSt_row (X : Ctx) (s : St) (b avr c cc pc tc : ℕ) (h : X.row b = (c, cc, pc, tc)) :
    (childSt X s b avr).unc = clr s.unc cc ∧
    (childSt X s b avr).cu = Nat.sub s.cu (X.cntF (Nat.land s.unc cc) 0) ∧
    (childSt X s b avr).nu = Nat.sub s.nu (fld s.cu c) := by
  unfold childSt; rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem fld_card (X : Ctx) (M : ℕ) (hW : X.W = M / 2) (hW15 : X.W < 2 ^ 15) (s : St) (hs : WF X M s)
    (c : ℕ) (hc : c ∈ Win M) :
    fld s.cu c = ((uncS M s).filter (fun j => cvr M j c)).card := by
  have hf : ∀ v < X.W + 1, ((uncS M s).filter (fun j => cvr M j v)).card < 2 ^ 16 := by
    intro v _
    have h1 : ((uncS M s).filter (fun j => cvr M j v)).card ≤ (uncS M s).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have := uncS_card_lt X M hW hW15 s
    omega
  rw [hs.cu]
  refine Eq.trans (EightV4.fld_sum (X.W + 1) (fun v => ((uncS M s).filter (fun j => cvr M j v)).card) hf c) ?_
  have := win_lt hc
  simp [show c < X.W + 1 by omega]

theorem cc_bit (M c j : ℕ) :
    (EightV4.compactOf ((Win M).filter (fun j => covM M j c))).testBit j =
      decide (j ∈ Win M ∧ covM M j c) := by
  rw [EightV4.testBit_compactOf]
  exact decide_eq_decide.mpr (by simp [mem_filter])

/-- the uncovered set of the child: the times not covered by the chosen class -/
theorem uncS_child (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (s : St) (c : ℕ)
    (hc : c ∈ AdmC (lvlMult i * p) p) (avr : ℕ) :
    uncS (lvlMult i * p) (childSt X s (2 ^ (16 * c)) avr) =
      (uncS (lvlMult i * p) s).filter (fun j => ¬ cvr (lvlMult i * p) j c) := by
  have hT' := hT
  obtain ⟨_, _, _, _, _, _, _, _, hrow, _, _⟩ := hT'
  obtain ⟨hu', _, _⟩ := childSt_row X s (2 ^ (16 * c)) avr c _ _ _ (hrow c hc)
  have hcW : c ∈ Win (lvlMult i * p) := (mem_filter.mp hc).1
  ext j
  simp only [uncS, hu', mem_filter, testBit_clr9, Bool.and_eq_true, Bool.not_eq_true', cc_bit, cvr,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨hjW, h1, h2⟩
    exact ⟨⟨hjW, h1⟩, fun h => h2 ⟨hjW, h.2⟩⟩
  · rintro ⟨⟨hjW, h1⟩, h2⟩
    exact ⟨hjW, h1, fun h => h2 ⟨hcW, h.2⟩⟩

theorem sub_arith (a n u' u : ℕ) (h1 : a ≤ u) (h2 : u' + n = u) : a - n ≤ u' := by omega

/-- **`child_state9` (counters).**  Taking the admissible class `c` preserves the counter invariant. -/
theorem wf_child (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (hW15 : X.W < 2 ^ 15) (s : St)
    (hs : WF X (lvlMult i * p) s) (c : ℕ) (hc : c ∈ AdmC (lvlMult i * p) p) (avr : ℕ) :
    WF X (lvlMult i * p) (childSt X s (2 ^ (16 * c)) avr) := by
  have hT' := hT
  obtain ⟨_, hWd, _, _, _, _, _, _, hrow, _, _⟩ := hT'
  have hcW : c ∈ Win (lvlMult i * p) := (mem_filter.mp hc).1
  obtain ⟨hu', hcu', hnu'⟩ := childSt_row X s (2 ^ (16 * c)) avr c _ _ _ (hrow c hc)
  have hnew : ∀ j, (Nat.land s.unc (EightV4.compactOf ((Win (lvlMult i * p)).filter
      (fun j => covM (lvlMult i * p) j c)))).testBit j = true → j ∈ Win (lvlMult i * p) := by
    intro j hj
    rw [testBit_land9] at hj
    exact hs.unc j (Bool.and_eq_true_iff.mp hj).1
  have hUc := uncS_child X i p hT s c hc avr
  have hcnt := cntF_spec X i p hT _ hnew
  have hfc := fld_card X _ hWd hW15 s hs c hcW
  obtain ⟨M, hM⟩ : ∃ M, M = lvlMult i * p := ⟨_, rfl⟩
  rw [← hM] at hUc hcnt hfc hnew hcW hs hWd hcu' ⊢
  have hNs : (Win M).filter (fun j => (Nat.land s.unc
      (EightV4.compactOf ((Win M).filter (fun j => covM M j c)))).testBit j = true) =
      (uncS M s).filter (fun j => cvr M j c) := by
    ext j
    simp only [mem_filter, testBit_land9, Bool.and_eq_true, cc_bit, uncS, cvr]
    constructor
    · rintro ⟨hjW, h1, h2⟩
      exact ⟨⟨hjW, h1⟩, hcW, (of_decide_eq_true h2).2⟩
    · rintro ⟨⟨hjW, h1⟩, _, h3⟩
      exact ⟨hjW, h1, decide_eq_true ⟨hjW, h3⟩⟩
  have hsplit : ∀ v, ((uncS M s).filter (fun j => cvr M j v)).card =
      (((uncS M s).filter (fun j => ¬ cvr M j c)).filter (fun j => cvr M j v)).card +
      (((uncS M s).filter (fun j => cvr M j c)).filter (fun j => cvr M j v)).card := by
    intro v
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (uncS M s).filter (fun j => cvr M j v)) (fun j => cvr M j c)
    rw [← this]
    have e1 : ((uncS M s).filter (fun j => cvr M j v)).filter (fun j => cvr M j c) =
        ((uncS M s).filter (fun j => cvr M j c)).filter (fun j => cvr M j v) := by
      ext j; simp only [mem_filter]; tauto
    have e2 : ((uncS M s).filter (fun j => cvr M j v)).filter (fun j => ¬ cvr M j c) =
        ((uncS M s).filter (fun j => ¬ cvr M j c)).filter (fun j => cvr M j v) := by
      ext j; simp only [mem_filter]; tauto
    rw [e1, e2, add_comm]
  have hcard : ((uncS M s).filter (fun j => ¬ cvr M j c)).card +
      ((uncS M s).filter (fun j => cvr M j c)).card = (uncS M s).card := by
    rw [add_comm]; exact Finset.filter_card_add_filter_neg_card_eq_card (s := uncS M s) (fun j => cvr M j c)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [hu', testBit_clr9] at hj
    exact hs.unc j (Bool.and_eq_true_iff.mp hj).1
  · rw [hUc, hcu', hcnt, hNs]
    have e : ∑ v ∈ range (X.W + 1), ((uncS M s).filter (fun j => cvr M j v)).card * 2 ^ (16 * v) =
        ∑ v ∈ range (X.W + 1), (((uncS M s).filter (fun j => ¬ cvr M j c)).filter
          (fun j => cvr M j v)).card * 2 ^ (16 * v) +
        ∑ v ∈ range (X.W + 1), (((uncS M s).filter (fun j => cvr M j c)).filter
          (fun j => cvr M j v)).card * 2 ^ (16 * v) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [hsplit v, add_mul]
    rw [hs.cu, e]
    exact Nat.add_sub_cancel _ _
  · rw [hUc, hnu', hfc]
    exact sub_arith _ _ _ _ hs.nu hcard

/-- the invariant of a root, a delegated state, or any state whose counters are recomputed from `unc` -/
theorem wf_of_unc (X : Ctx) (i p : ℕ) (hT : TableOK9g X i p) (s : St)
    (hu : ∀ j, s.unc.testBit j = true → j ∈ Win (lvlMult i * p)) (hcu : s.cu = X.cntF s.unc 0)
    (hnu : s.nu ≤ (uncS (lvlMult i * p) s).card) : WF X (lvlMult i * p) s :=
  ⟨hu, by rw [hcu]; exact cntF_spec X i p hT s.unc hu, hnu⟩

theorem pcl_eq9 : ∀ (f u acc : ℕ), pcl f u acc = EightV4.pcl f u acc
  | 0, u, acc => rfl
  | f + 1, u, acc => by
    show (bif Nat.beq u 0 then acc else pcl f (Nat.land u (Nat.sub u 1)) (Nat.succ acc)) =
      (bif Nat.beq u 0 then acc else EightV4.pcl f (Nat.land u (Nat.sub u 1)) (Nat.succ acc))
    rw [pcl_eq9 f]

/-- `pcl` never overcounts: the counter `nu` recomputed by `pcl` is at most the number of uncovered times -/
theorem pcl_nu_le (M u : ℕ) (hu : ∀ j, u.testBit j = true → j ∈ Win M) (f : ℕ) :
    pcl f u 0 ≤ ((Win M).filter (fun j => u.testBit j = true)).card := by
  have hK : u < 2 ^ (M / 2 + 1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_contra hne
    have h1 : u.testBit i = true := by simpa using hne
    have := win_lt (hu i h1)
    omega
  have h := EightV4.pcl_le (M / 2 + 1) f u 0 hK
  have hsub : (range (M / 2 + 1)).filter (fun i => u.testBit i = true) ⊆
      (Win M).filter (fun j => u.testBit j = true) := by
    intro i hi
    simp only [mem_filter] at hi ⊢
    exact ⟨hu i hi.2, hi.2⟩
  have := Finset.card_le_card hsub
  rw [pcl_eq9]
  omega

end LRSpectrumFull.NineSound
