/-
# Nine runners, soundness part 3d: the level-2 semantic predicate `Cmp2`, the transfer `t12`, infeasible roots

`Cmp2 X p V s` (modulus `9p`, classes `V`): counter invariant `WF`; chosen classes `C <= V`; unsatisfied items
`I <= D0` (classes mod `p`, `im`, `mp`) and `T <= D1` (classes mod `3p`, `it`, `mq` for the non-multiples of 3,
`mf` for the multiples of 3); the slot count `|I| + |T| + |C| + fr = 8`; `c3 = |T /\\ 3Z| + |C /\\ 3Z| <= 6`; every
unsatisfied item has a witness element of `V` not yet chosen (an element over a `p`-item is not over a chosen
`3p`-item, so the witnesses of distinct items are distinct); the lifts of unsatisfied `p`-items and `3p`-items are
disjoint (`not (PM p c t)`); `V \\ C` covers the uncovered times.

`t12`: a level-1 leaf in `Cmp1` lifts its descriptor `(im, ch, fr)` to a level-2 root in `Cmp2` (`I = I1`,
`T = C1`, `C = {}`).  `inf1`, `inf2`: a root with more than 6 forced multiples of 3 contradicts `Cmp1`, `Cmp2`
(`d1_three`: `D1` has at most 6 multiples of 3).  `hr1`, `hr2`: `r != 99`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Level1

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

def Cmp2 (X : Ctx) (p : ℕ) (V : Finset ℕ) (s : St) : Prop :=
  WF X (9 * p) s ∧ ∃ C I T : Finset ℕ,
    s.ch = EightV4.spreadOf C ∧ s.im = EightV4.spreadOf I ∧ s.it = EightV4.spreadOf T ∧ C ⊆ V ∧
    I ⊆ D0 p V ∧ T ⊆ D1 p V ∧ I.card + T.card + C.card + s.fr = 8 ∧ C.card + s.r = 8 ∧
    s.mp = EightV4.spreadOf (liftSet (9 * p) p p I) ∧
    s.mq = EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c))) ∧
    s.mf = EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c))) ∧
    s.c3 = (T.filter (fun c => 3 ∣ c)).card + (C.filter (fun c => 3 ∣ c)).card ∧ s.c3 ≤ 6 ∧
    (∀ x, bitS s.av x = true → x ∉ C) ∧ (∀ y ∈ V, y ∉ C → bitS s.av y = true) ∧
    (∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ v ∉ C ∧ red (3 * p) v ∉ T) ∧
    (∀ t ∈ T, ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ C) ∧ (∀ c ∈ I, ∀ t ∈ T, ¬ PM p c t) ∧
    (∀ j ∈ uncS (9 * p) s, ∃ y ∈ V, y ∉ C ∧ covM (9 * p) j y)

theorem lv2 (p : ℕ) : lvlMult 2 * p = 9 * p := by simp [lvlMult]

theorem adm_mono' {M M' p x : ℕ} (h : M ≤ M') (hx : x ∈ AdmC M p) : x ∈ AdmC M' p := by
  simp only [AdmC, Win, mem_filter, mem_Icc] at hx ⊢
  have := Nat.div_le_div_right (c := 2) h
  omega

theorem d1_three {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) :
    ((D1 p V).filter (fun x => 3 ∣ x)).card ≤ 6 := by
  have hsub : (D1 p V).filter (fun x => 3 ∣ x) ⊆ (V.filter (fun x => 3 ∣ x)).image (red (3 * p)) := by
    intro y hy
    obtain ⟨hyD, h3⟩ := mem_filter.mp hy
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hyD
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv,
      (red_dvd 3 (3 * p) v (by omega) (dvd_mul_right 3 p)).1 h3⟩, rfl⟩
  exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hV.side)

theorem leafOK1_desc (X : Ctx) (hlvl : X.lvl = 1) (nx : ℕ → ℕ × ℕ × ℕ) (s : St) (i : ℕ)
    (h : leafOK X nx s i = true) :
    s.unc = 0 ∧ (nx i).1 = s.im ∧ (nx i).2.1 = s.ch ∧ (nx i).2.2 = s.fr := by
  unfold leafOK at h
  rcases hnx : nx i with ⟨a, b, c⟩
  rw [hnx] at h
  have h0 : Nat.beq X.lvl 0 = false := by rw [hlvl]; rfl
  have h2 : ltN X.lvl 2 = true := by rw [hlvl]; rfl
  simp only [h0, h2, cond_false, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h3, h4, h5⟩

/-- **`t12`: a level-1 leaf in `Cmp1` lifts its descriptor to a level-2 root in `Cmp2`.** -/
theorem t12 {X1 X2 : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 1 < p) (hV : Good9 p V)
    (hT1 : TableOK9g X1 1 p) (hT2 : TableOK9g X2 2 p) (hW : X2.W + 1 < 2 ^ 16)
    (nx2 : ℕ → ℕ × ℕ × ℕ) (s : St) (i : ℕ) (hs : Cmp1 X1 p V s) (hl : leafOK X1 nx2 s i = true) :
    Cmp2 X2 p V (rootSt X2 (nx2 i).1 (nx2 i).2.1 (nx2 i).2.2) := by
  obtain ⟨hlvl, _⟩ := hT1
  obtain ⟨_, hd1, hd2, hd3⟩ := leafOK1_desc X1 hlvl nx2 s i hl
  obtain ⟨_, C, I, hch, him, hCD, hID, hcard, hr, hit, hmq, hmf, hmp, hc3, hdis, hav, hwit, hdisj,
    hcov⟩ := hs
  rw [hd1, hd2, hd3, him, hch]
  have hIsub : I ⊆ AdmC (9 * p) p := fun x hx =>
    adm_mono' (show p ≤ 9 * p by omega) (d0_adm (by omega) hV (hID hx))
  have hTsub : C ⊆ AdmC (9 * p) p := fun x hx =>
    adm_mono' (show 3 * p ≤ 9 * p by omega) (d1_adm (by omega) hV (hCD hx))
  have hI8 : I.card ≤ 16 := by have := Finset.card_le_card hID; have := d0_card hV; omega
  have hC8 : C.card ≤ 8 := by have := Finset.card_le_card hCD; have := d1_card hV; omega
  obtain ⟨hmp2, hmq2, hmf2, hc32, -, hr2⟩ := rootSt_masks X2 p hT2 hW I C hIsub hTsub hI8
    (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by omega))
    (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by omega)) s.fr
  have hT2' := hT2
  obtain ⟨_, _, _, hadm, _⟩ := hT2'
  rw [lv2] at hadm
  have h3 : (C.filter (fun c => 3 ∣ c)).card ≤ 6 :=
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hCD)) (d1_three (by omega) hV)
  refine ⟨wf_rootSt (lv2 p) hT2 _ _ _, ∅, I, C, rfl, rfl, rfl, Finset.empty_subset _, hID, hCD, ?_, ?_,
    hmp2, hmq2, hmf2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show I.card + C.card + (∅ : Finset ℕ).card + s.fr = 8; simp; omega
  · show (∅ : Finset ℕ).card + (rootSt X2 _ _ _).r = 8; rw [hr2]; simp
  · rw [hc32]; simp
  · show (rootSt X2 _ _ _).c3 ≤ 6; rw [hc32]; exact h3
  · intro x _ h; simp at h
  · intro y hy _
    show bitS X2.adm y = true
    rw [hadm]
    simp only [bitS, tb_sp, decide_eq_true_eq]
    exact hV.adm hy
  · intro c hc
    obtain ⟨v, hv, hred, hnot⟩ := hwit c hc
    exact ⟨v, hv, hred, by simp, hnot⟩
  · intro t ht
    obtain ⟨v, hv, hred⟩ := mem_image.mp (hCD ht)
    exact ⟨v, hv, hred, by simp⟩
  · intro c hc t ht; exact hdisj c hc t ht
  · intro j hj
    exact (fun ⟨y, hy, hc⟩ => ⟨y, hy, by simp, hc⟩) (hV.cover j (mem_filter.mp hj).1)

/-- an infeasible level-1 root (more than 6 forced multiples of 3) contradicts `Cmp1` -/
theorem inf1 {X1 : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) (d : ℕ × ℕ × ℕ)
    (h : Cmp1 X1 p V (rootSt X1 d.1 d.2.1 d.2.2))
    (hl : ltN 6 (spc X1 (Nat.land d.2.1 X1.m3)) = true) : False := by
  obtain ⟨_, C, I, _, _, hCD, _, _, _, _, _, _, _, hc3, _⟩ := h
  have h3 : (C.filter (fun c => 3 ∣ c)).card ≤ 6 :=
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hCD)) (d1_three hp hV)
  have h4 : (rootSt X1 d.1 d.2.1 d.2.2).c3 = spc X1 (Nat.land d.2.1 X1.m3) := rfl
  rw [← h4, hc3] at hl
  rw [ltN_eq9] at hl
  have := of_decide_eq_true hl
  omega

theorem inf2 {X2 : Ctx} {p : ℕ} {V : Finset ℕ} (d : ℕ × ℕ × ℕ)
    (h : Cmp2 X2 p V (rootSt X2 d.1 d.2.1 d.2.2))
    (hl : ltN 6 (spc X2 (Nat.land d.2.1 X2.m3)) = true) : False := by
  obtain ⟨_, C, I, T, _, _, _, _, _, _, _, _, _, _, _, _, h6, _⟩ := h
  have h4 : (rootSt X2 d.1 d.2.1 d.2.2).c3 = spc X2 (Nat.land d.2.1 X2.m3) := rfl
  rw [← h4] at hl
  rw [ltN_eq9] at hl
  have := of_decide_eq_true hl
  omega

theorem hr1 {X : Ctx} {p : ℕ} {V : Finset ℕ} (s : St) (hs : Cmp1 X p V s) (i : ℕ) :
    stEq (noH i) s = false := by
  obtain ⟨_, C, _, _, _, _, _, _, hCr, _⟩ := hs
  exact stEq_noH_false s (by omega) i

theorem hr2 {X : Ctx} {p : ℕ} {V : Finset ℕ} (s : St) (hs : Cmp2 X p V s) (i : ℕ) :
    stEq (noH i) s = false := by
  obtain ⟨_, C, _, _, _, _, _, _, _, _, hCr, _⟩ := hs
  exact stEq_noH_false s (by omega) i

end LRSpectrumFull.NineSound
