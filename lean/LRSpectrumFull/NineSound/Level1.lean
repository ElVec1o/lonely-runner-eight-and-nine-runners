/-
# Nine runners, soundness part 3c: the level-1 semantic predicate `Cmp1` and the transfer `t01`

A level-0 leaf in `Cmp0` has chosen classes `C0 <= D0` (`ch`), `|C0| + r = 8` and `fr = r`, and the descriptor
of the level-1 tree is `(ch, 0, fr)`.  The level-1 root has the items `I = C0` (classes mod `p` that must be
served by a pick `= +-c mod p` of level 1), `|I| + |C| + fr = 8` with `C = {}`.

`Cmp1 X p V s` (modulus `3p`, classes `D1 p V = fold_{3p}(V)`):  counter invariant `WF`; chosen level-1 classes `C`
inside `D1`; unsatisfied items `I` (`im`) inside `D0`, each with a witness `v` of `V` over it whose `3p`-fold is
not yet chosen; the slot count `|I| + |C| + fr = 8` and `|C| + r = 8`; the item mask `mp` is the spread of the
lifts of `I`; no `3p`-items (`it = mq = mf = 0`); `c3` counts the chosen multiples of 3; no chosen class lies over
an unsatisfied item; the available mask contains `D1 \ C` and misses `C`; `D1 \ C` covers the uncovered times.

Proved here: `rootSt1_masks` (the item mask of a level-1 root), `wf_rootSt` (counter invariant of any root),
`d1_adm`, `d1_cover` (the projection of `V` to `3p`), `leafOK0_desc`, and
**`t01`**: a level-0 leaf in `Cmp0` lifts its descriptor to a level-1 root in `Cmp1` (the slot accounting
`|I| + |C| + fr = 8` is `|C0| + 0 + fr = 8`, with the witnesses coming from the folds of the elements of `V`).
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Level0

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

def Cmp1 (X : Ctx) (p : ℕ) (V : Finset ℕ) (s : St) : Prop :=
  WF X (3 * p) s ∧ ∃ C I : Finset ℕ,
    s.ch = EightV4.spreadOf C ∧ s.im = EightV4.spreadOf I ∧ C ⊆ D1 p V ∧ I ⊆ D0 p V ∧
    I.card + C.card + s.fr = 8 ∧ C.card + s.r = 8 ∧ s.it = 0 ∧ s.mq = 0 ∧ s.mf = 0 ∧
    s.mp = EightV4.spreadOf (liftSet (3 * p) p p I) ∧ s.c3 = (C.filter (fun x => 3 ∣ x)).card ∧
    (∀ x, bitS s.av x = true → x ∉ C) ∧ (∀ y ∈ D1 p V, y ∉ C → bitS s.av y = true) ∧
    (∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ red (3 * p) v ∉ C) ∧ (∀ c ∈ I, ∀ y ∈ C, ¬ PM p c y) ∧
    (∀ j ∈ uncS (3 * p) s, ∃ y ∈ D1 p V, y ∉ C ∧ covM (3 * p) j y)

theorem lv1 (p : ℕ) : lvlMult 1 * p = 3 * p := by simp [lvlMult]

theorem d1_adm {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) : D1 p V ⊆ AdmC (3 * p) p := by
  intro y hy
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
  exact adm_of_red p (3 * p) v (by omega) (dvd_mul_left p 3) (not_dvd_of_adm (hV.adm hv)) hp

theorem d1_card {p : ℕ} {V : Finset ℕ} (hV : Good9 p V) : (D1 p V).card ≤ 8 :=
  le_trans Finset.card_image_le hV.card

theorem d1_cover {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hp2 : p % 2 = 1) (hV : Good9 p V) :
    ∀ j ∈ Win (3 * p), ∃ y ∈ D1 p V, covM (3 * p) j y := by
  intro j hj
  have hD : ∀ j ∈ Win (3 * (3 * p)), ∃ x ∈ V, covM (3 * (3 * p)) j x := by
    rw [show 3 * (3 * p) = 9 * p by ring]; exact hV.cover
  obtain ⟨x, hx, hcov⟩ := proj_cover 3 (3 * p) (by norm_num) (by omega) V hD j hj
  exact ⟨red (3 * p) x, mem_image_of_mem _ hx, (covM_red (3 * p) j x (by omega)).2 hcov⟩

theorem adm_mono {p x : ℕ} (hx : x ∈ AdmC p p) : x ∈ AdmC (3 * p) p := by
  simp only [AdmC, Win, mem_filter, mem_Icc] at hx ⊢
  omega

theorem orRows_zero (X : Ctx) (sel : ℕ × ℕ × ℕ × ℕ → ℕ) (f acc : ℕ) : orRows X sel (f + 1) 0 acc = acc := rfl

/-- **The item mask of a level-1 root.** -/
theorem rootSt1_masks {X : Ctx} {p : ℕ} (hT : TableOK9g X 1 p) (I : Finset ℕ)
    (hI : I ⊆ AdmC (3 * p) p) (h1 : I.card ≤ 16) (fr : ℕ) :
    (rootSt X (EightV4.spreadOf I) 0 fr).mp = EightV4.spreadOf (liftSet (3 * p) p p I) ∧
    (rootSt X (EightV4.spreadOf I) 0 fr).mq = 0 ∧ (rootSt X (EightV4.spreadOf I) 0 fr).mf = 0 ∧
    (rootSt X (EightV4.spreadOf I) 0 fr).c3 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hrow, _, _⟩ := hT
  rw [lv1] at hrow
  have e0 : ∀ x, Nat.lor 0 x = x := fun x => Nat.zero_or x
  have hz : clr 0 X.m3 = 0 := by simp [clr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show orRows X (fun t => t.2.2.1) 16 (EightV4.spreadOf I) 0 = _
    rw [orRows_spec X (fun t => t.2.2.1) (fun x => (AdmC (3 * p) p).filter (fun y => PM p x y)) 16 I 0
      h1 (fun x hx => by rw [hrow x (hI hx)]; simp)]
    simp only [e0]
    congr 1; ext y
    simp only [liftSet, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨c, hc, hy, hpm⟩; exact ⟨hy, c, hc, hpm⟩
    · rintro ⟨hy, c, hc, hpm⟩; exact ⟨c, hc, hy, hpm⟩
  · show orRows X (fun t => t.2.2.2) 16 (clr 0 X.m3) 0 = 0
    rw [hz]; exact orRows_zero X _ 15 0
  · show orRows X (fun t => t.2.2.2) 16 (Nat.land 0 X.m3) 0 = 0
    rw [show Nat.land 0 X.m3 = 0 by simp [Nat.land_eq]]; exact orRows_zero X _ 15 0
  · show spc X (Nat.land 0 X.m3) = 0
    rw [show Nat.land 0 X.m3 = 0 by simp [Nat.land_eq]]; simp [spc]

/-- **The counter invariant of a root state** (any level, any descriptor). -/
theorem wf_rootSt {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p)
    (icm ict fr : ℕ) : WF X M (rootSt X icm ict fr) := by
  have hT' := hT
  obtain ⟨_, hWd, hfull, _⟩ := hT'
  subst hM
  have hfull' : ∀ j, X.full.testBit j = decide (j ∈ Win (lvlMult i * p)) := by
    intro j; rw [hfull, EightV4.testBit_compactOf]
  have hu : ∀ j, (rootSt X icm ict fr).unc.testBit j = true → j ∈ Win (lvlMult i * p) := by
    intro j hj
    have : X.full.testBit j = true := hj
    rw [hfull'] at this; exact of_decide_eq_true this
  refine wf_of_unc X i p hT _ hu rfl ?_
  have hU : uncS (lvlMult i * p) (rootSt X icm ict fr) = Win (lvlMult i * p) := by
    ext j
    simp only [uncS, mem_filter]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, by show X.full.testBit j = true; rw [hfull']; exact decide_eq_true h⟩
  rw [hU]
  show X.W ≤ _
  simp only [Win, Nat.card_Icc]
  omega

theorem leafOK0_desc (X : Ctx) (hlvl : X.lvl = 0) (nx : ℕ → ℕ × ℕ × ℕ) (s : St) (i : ℕ)
    (h : leafOK X nx s i = true) :
    s.unc = 0 ∧ (nx i).1 = s.ch ∧ (nx i).2.1 = 0 ∧ (nx i).2.2 = s.fr := by
  unfold leafOK at h
  rcases hnx : nx i with ⟨a, b, c⟩
  rw [hnx] at h
  have h0 : Nat.beq X.lvl 0 = true := by rw [hlvl]; rfl
  have h2 : ltN X.lvl 2 = true := by rw [hlvl]; rfl
  simp only [h0, h2, cond_true, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h3, h4, h5⟩

/-- **`t01`: a level-0 leaf in `Cmp0` lifts its descriptor to a level-1 root in `Cmp1`.** -/
theorem t01 {X0 X1 : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 1 < p) (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT0 : TableOK9g X0 0 p) (hT1 : TableOK9g X1 1 p) (nx1 : ℕ → ℕ × ℕ × ℕ) (s : St) (i : ℕ)
    (hs : Cmp0 X0 p V s) (hl : leafOK X0 nx1 s i = true) :
    Cmp1 X1 p V (rootSt X1 (nx1 i).1 (nx1 i).2.1 (nx1 i).2.2) := by
  obtain ⟨hlvl, _⟩ := hT0
  obtain ⟨_, hd1, hd2, hd3⟩ := leafOK0_desc X0 hlvl nx1 s i hl
  obtain ⟨_, C, hch, hCD, hCr, hfr, -⟩ := hs
  rw [hd1, hd2, hd3, hch]
  have hCsub : C ⊆ AdmC (3 * p) p := fun x hx => adm_mono (d0_adm (by omega) hV (hCD hx))
  have hC8 : C.card ≤ 16 := by
    have := Finset.card_le_card hCD
    have := d0_card hV
    omega
  obtain ⟨hmp, hmq, hmf, hc3⟩ := rootSt1_masks hT1 C hCsub hC8 s.fr
  have hT1' := hT1
  obtain ⟨_, _, _, hadm, _⟩ := hT1'
  rw [lv1] at hadm
  refine ⟨wf_rootSt (lv1 p) hT1 _ _ _, ∅, C, rfl, rfl, Finset.empty_subset _, hCD, ?_, ?_, rfl, hmq, hmf,
    hmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show C.card + (∅ : Finset ℕ).card + s.fr = 8; simp; omega
  · show (∅ : Finset ℕ).card + 8 = 8; simp
  · rw [hc3]; simp
  · intro x _ h; simp at h
  · intro y hy _
    show bitS X1.adm y = true
    rw [hadm]
    simp only [bitS, tb_sp, decide_eq_true_eq]
    exact d1_adm (by omega) hV hy
  · intro c hc
    obtain ⟨v, hv, hred⟩ := mem_image.mp (hCD hc)
    exact ⟨v, hv, hred, by simp⟩
  · intro c _ y hy; simp at hy
  · intro j hj
    have hj' : j ∈ Win (3 * p) := (mem_filter.mp hj).1
    obtain ⟨y, hyD, hcy⟩ := d1_cover (by omega) hp2 hV j hj'
    exact ⟨y, hyD, by simp, hcy⟩

end LRSpectrumFull.NineSound
