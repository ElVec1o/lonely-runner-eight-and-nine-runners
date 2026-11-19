/-
# Nine runners, soundness part 3b: the semantic predicate `Cmp0` of the level-0 tree (modulus `p`)

`Good9 p V`: `V` is a set of at most 8 admissible classes mod `9p`, at most 6 of them multiples of 3, covering
the window of `9p` (the data a counterexample to `lemma7Check 8 p` gives; unit normalisation: some class of `V`
folds to the class 1 mod `p`).  `D0 p V = {fold_p v : v in V}` is the set of its level-0 classes.

`Cmp0 X p V s` is the semantic notion of "good class set" at level 0: `s` has the counter invariant `WF`, its
chosen classes `C` (`ch`) lie in `D0`, `|C| + r = 8`, `fr = r`, no item masks, the available classes `av` are
disjoint from `C` and contain `D0 \ C`, and `D0 \ C` covers the uncovered times.  The canonical
completion is `Z = D0 \ C`.

Proved here (part 3b, all generic in `V`):
* `sem0`      `Sem X0 (Cmp0 X0 p V)`: `bound` and `nocov` from `Sem9`, and `branch` (the least coverer `z` of `D0 \ C`
              of the uncovered time `j`; the sibling exclusion never removes a class of `D0 \ C` other than `z`);
* `hdel0`     the delegation transfer (`stEq h s` gives `Cmp0` for the recomputed counters);
* `hr0`       `r != 99` on `Cmp0`;
* `hroot0`    `Cmp0 X0 p V (root0 X0)`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Sem9
import LRSpectrumFull.NineSound.Hier

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

structure Good9 (p : ℕ) (V : Finset ℕ) : Prop where
  adm : V ⊆ AdmC (9 * p) p
  card : V.card ≤ 8
  cover : ∀ j ∈ Win (9 * p), ∃ x ∈ V, covM (9 * p) j x
  side : (V.filter (fun x => 3 ∣ x)).card ≤ 6
  norm : ∃ v ∈ V, red p v = 1

def D0 (p : ℕ) (V : Finset ℕ) : Finset ℕ := V.image (red p)
def D1 (p : ℕ) (V : Finset ℕ) : Finset ℕ := V.image (red (3 * p))

theorem not_dvd_of_adm {p x M : ℕ} (hx : x ∈ AdmC M p) : ¬ p ∣ x :=
  fun h => (mem_filter.mp hx).2 (Nat.mod_eq_zero_of_dvd h)

theorem adm_of_red (p M x : ℕ) (hM : 0 < M) (hpM : p ∣ M) (hx : ¬ p ∣ x) (hp : 0 < p) :
    red M x ∈ AdmC M p := by
  obtain ⟨h1, h2, h3⟩ := red_mem p M x hM hpM hx
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, h2⟩, fun h => h3 (Nat.dvd_of_mod_eq_zero h)⟩

theorem d0_adm {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) : D0 p V ⊆ AdmC p p := by
  intro y hy
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
  exact adm_of_red p p v hp (dvd_refl p) (not_dvd_of_adm (hV.adm hv)) hp

theorem d0_card {p : ℕ} {V : Finset ℕ} (hV : Good9 p V) : (D0 p V).card ≤ 8 :=
  le_trans Finset.card_image_le hV.card

theorem d0_cover {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hp2 : p % 2 = 1) (hV : Good9 p V) :
    ∀ j ∈ Win p, ∃ y ∈ D0 p V, covM p j y := by
  intro j hj
  obtain ⟨x, hx, hcov⟩ := proj_cover 9 p (by norm_num) hp2 V hV.cover j hj
  exact ⟨red p x, mem_image_of_mem _ hx, (covM_red p j x hp).2 hcov⟩

/-! ## M-general wrappers of the `Sem9` lemmas -/

theorem wf_child_M {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p)
    (hW15 : X.W < 2 ^ 15) (s : St) (hs : WF X M s) (c : ℕ) (hc : c ∈ AdmC M p) (avr : ℕ) :
    WF X M (childSt X s (2 ^ (16 * c)) avr) := by
  subst hM; exact wf_child X i p hT hW15 s hs c hc avr

theorem uncS_child_M {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p)
    (s : St) (c : ℕ) (hc : c ∈ AdmC M p) (avr : ℕ) :
    uncS M (childSt X s (2 ^ (16 * c)) avr) = (uncS M s).filter (fun j => ¬ cvr M j c) := by
  subst hM; exact uncS_child X i p hT s c hc avr

theorem wf_of_unc_M {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p) (s : St)
    (hu : ∀ j, s.unc.testBit j = true → j ∈ Win M) (hcu : s.cu = X.cntF s.unc 0)
    (hnu : s.nu ≤ (uncS M s).card) : WF X M s := by
  subst hM; exact wf_of_unc X i p hT s hu hcu hnu

theorem sem_mk_M {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p)
    (hW15 : X.W < 2 ^ 15) (Cmp : St → Prop)
    (hG : ∀ s, Cmp s → WF X M s ∧ Compl X M s)
    (hbr : ∀ (s : St) (j : ℕ), Cmp s → bitC s.unc j = true →
      ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
        ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
          !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
          Cmp (childSt X s (2 ^ e) avr)) : Sem X Cmp := by
  subst hM; exact sem_mk X i p hT hW15 Cmp hG hbr

theorem cb_bit_M {X : Ctx} {i p M : ℕ} (hM : lvlMult i * p = M) (hT : TableOK9g X i p) {j : ℕ}
    (hj : j ∈ Win M) (v : ℕ) : (X.cbJ j).testBit (16 * v) = decide (cvr M j v) := by
  subst hM; exact cb_bit hT hj v

/-! ## Level-0 table facts -/

theorem lv0 (p : ℕ) : lvlMult 0 * p = p := by simp [lvlMult]

theorem row0 {X : Ctx} {p : ℕ} (hT : TableOK9g X 0 p) (x : ℕ) (hx : x ∈ AdmC p p) :
    X.row (2 ^ (16 * x)) =
      (x, EightV4.compactOf ((Win p).filter (fun j => covM p j x)), 0, 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrow, _, _⟩ := hT
  have := hrow x (by rw [lv0]; exact hx)
  rw [lv0] at this
  simpa using this

theorem m3_0 {X : Ctx} {p : ℕ} (hT : TableOK9g X 0 p) : X.m3 = 0 := by
  obtain ⟨_, _, _, _, hm3, _⟩ := hT
  simpa using hm3

theorem allowed0 (X : Ctx) (s : St) (hm3 : X.m3 = 0) (hmp : s.mp = 0) (hmq : s.mq = 0)
    (hmf : s.mf = 0) (hc3 : s.c3 = 0) (hfr : s.fr ≠ 0) : allowed X s = s.av := by
  have hb : Nat.beq s.fr 0 = false := beq_zero_false _ hfr
  unfold allowed
  simp [hm3, hmp, hmq, hmf, hc3, hb, clr, ltN]

theorem childSt_noitems (X : Ctx) (s : St) (b avr c cc : ℕ) (h : X.row b = (c, cc, 0, 0))
    (hm3 : X.m3 = 0) (hmp : s.mp = 0) (hmq : s.mq = 0) (hmf : s.mf = 0) (him : s.im = 0)
    (hit : s.it = 0) (hc3 : s.c3 = 0) :
    (childSt X s b avr).ch = Nat.lor s.ch b ∧ (childSt X s b avr).fr = s.fr - 1 ∧
    (childSt X s b avr).r = s.r - 1 ∧ (childSt X s b avr).c3 = 0 ∧ (childSt X s b avr).im = 0 ∧
    (childSt X s b avr).it = 0 ∧ (childSt X s b avr).mp = 0 ∧ (childSt X s b avr).mq = 0 ∧
    (childSt X s b avr).mf = 0 ∧ (childSt X s b avr).av = avr := by
  unfold childSt
  rw [h]
  simp [nz, hm3, hmp, hmq, hmf, him, hit, hc3, Nat.land_eq]

/-! ## The semantic predicate -/

def Cmp0 (X : Ctx) (p : ℕ) (V : Finset ℕ) (s : St) : Prop :=
  WF X p s ∧ ∃ C : Finset ℕ, s.ch = EightV4.spreadOf C ∧ C ⊆ D0 p V ∧ C.card + s.r = 8 ∧
    s.fr = s.r ∧ s.im = 0 ∧ s.it = 0 ∧ s.mp = 0 ∧ s.mq = 0 ∧ s.mf = 0 ∧ s.c3 = 0 ∧
    (∀ x, bitS s.av x = true → x ∉ C) ∧ (∀ y ∈ D0 p V, y ∉ C → bitS s.av y = true) ∧
    (∀ j ∈ uncS p s, ∃ y ∈ D0 p V, y ∉ C ∧ covM p j y)

theorem win_of_d0 {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) {y : ℕ} (hy : y ∈ D0 p V) :
    y ∈ Win p := (mem_filter.mp (d0_adm hp hV hy)).1

/-- the canonical completion `D0 \ C` -/
theorem good0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V)
    (hT : TableOK9g X 0 p) (s : St) (hs : Cmp0 X p V s) : WF X p s ∧ Compl X p s := by
  obtain ⟨hwf, C, hch, hCD, hCr, hfr, him, hit, hmp, hmq, hmf, hc3, hdis, hav, hcov⟩ := hs
  refine ⟨hwf, D0 p V \ C, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvD, hvC⟩ := mem_sdiff.mp hv
    have hcard : (D0 p V \ C).card ≤ s.r := by
      rw [Finset.card_sdiff_of_subset hCD]
      have := d0_card hV
      omega
    have hpos : 0 < (D0 p V \ C).card := Finset.card_pos.mpr ⟨v, hv⟩
    have hfr0 : s.fr ≠ 0 := by omega
    refine ⟨win_of_d0 hp hV hvD, ?_⟩
    rw [allowed0 X s (m3_0 hT) hmp hmq hmf hc3 hfr0]
    exact hav v hvD hvC
  · rw [Finset.card_sdiff_of_subset hCD]
    have := d0_card hV
    omega
  · intro j hj
    obtain ⟨y, hyD, hyC, hcy⟩ := hcov j hj
    exact ⟨y, mem_sdiff.mpr ⟨hyD, hyC⟩, hcy⟩

theorem spreadOf_single (z : ℕ) : EightV4.spreadOf ({z} : Finset ℕ) = 2 ^ (16 * z) := by
  simp [EightV4.spreadOf]

/-- **`Sem.branch` at level 0.** -/
theorem hbr0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) (hT : TableOK9g X 0 p)
    (hW15 : X.W < 2 ^ 15) (s : St) (j : ℕ) (hs : Cmp0 X p V s) (hj : bitC s.unc j = true) :
    ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
      ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
        !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
        Cmp0 X p V (childSt X s (2 ^ e) avr) := by
  have hs' := hs
  obtain ⟨hwf, C, hch, hCD, hCr, hfr, him, hit, hmp, hmq, hmf, hc3, hdis, hav, hcov⟩ := hs'
  rw [bitC_eq9] at hj
  have hjW := hwf.unc j hj
  have hjU : j ∈ uncS p s := mem_filter.mpr ⟨hjW, hj⟩
  obtain ⟨y0, hy0D, hy0C, hy0cov⟩ := hcov j hjU
  have hr1 : 1 ≤ s.r := by
    have h1 : 0 < (D0 p V \ C).card := Finset.card_pos.mpr ⟨y0, mem_sdiff.mpr ⟨hy0D, hy0C⟩⟩
    rw [Finset.card_sdiff_of_subset hCD] at h1
    have := d0_card hV
    omega
  have hfr0 : s.fr ≠ 0 := by omega
  have hal := allowed0 X s (m3_0 hT) hmp hmq hmf hc3 hfr0
  have hne : ((D0 p V).filter (fun y => y ∉ C ∧ covM p j y)).Nonempty :=
    ⟨y0, mem_filter.mpr ⟨hy0D, hy0C, hy0cov⟩⟩
  have hzY := Finset.min'_mem _ hne
  have hzle : ∀ y ∈ (D0 p V).filter (fun y => y ∉ C ∧ covM p j y),
      ((D0 p V).filter (fun y => y ∉ C ∧ covM p j y)).min' hne ≤ y :=
    fun y hy => Finset.min'_le _ y hy
  generalize ((D0 p V).filter (fun y => y ∉ C ∧ covM p j y)).min' hne = z at hzY hzle
  obtain ⟨hzD, hzC, hzcov⟩ := mem_filter.mp hzY |> fun h => (⟨h.1, h.2.1, h.2.2⟩ : _ ∧ _ ∧ _)
  have hzadm : z ∈ AdmC p p := d0_adm hp hV hzD
  have hzW : z ∈ Win p := (mem_filter.mp hzadm).1
  have hmbit : ∀ y, (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = true ↔
      (cvr p j y ∧ bitS s.av y = true) := by
    intro y
    rw [testBit_land9, cb_bit_M (lv0 p) hT hjW, hal]
    simp [bitS]
  have hmz := (hmbit z).mpr ⟨⟨hzW, hzcov⟩, hav z hzD hzC⟩
  refine ⟨16 * z, hmz, ?_⟩
  intro avr havr
  obtain ⟨hch', hfr', hr', hc3', him', hit', hmp', hmq', hmf', hav'⟩ :=
    childSt_noitems X s (2 ^ (16 * z)) avr z _ (row0 hT z hzadm) (m3_0 hT) hmp hmq hmf him hit hc3
  refine ⟨wf_child_M (lv0 p) hT hW15 s hwf z hzadm avr, insert z C, ?_, ?_, ?_, ?_, him', hit', hmp',
    hmq', hmf', hc3', ?_, ?_, ?_⟩
  · rw [hch', hch, show Nat.lor (EightV4.spreadOf C) (2 ^ (16 * z)) =
        Nat.lor (2 ^ (16 * z)) (EightV4.spreadOf C) from Nat.lor_comm _ _, Finset.insert_eq,
      ← spreadOf_single z, spreadOf_lor]
  · exact Finset.insert_subset_iff.mpr ⟨hzD, hCD⟩
  · rw [Finset.card_insert_of_notMem hzC, hr']; omega
  · rw [hfr', hr']; omega
  · intro x hx hmem
    rw [hav'] at hx
    have h1 : avr.testBit (16 * x) = true := hx
    rw [havr, Bool.and_eq_true] at h1
    rcases mem_insert.mp hmem with hxz | hxC
    · rw [hxz] at h1
      have := h1.2
      rw [hmz] at this
      simp at this
    · have := h1.1
      have h2 := hdis x
      simp only [bitS] at h2
      exact absurd (h2 this) (by simpa using hxC)
  · intro y hyD hyC
    rw [hav']
    have hyC' : y ∉ C := fun h => hyC (mem_insert_of_mem h)
    have hyz : y ≠ z := fun h => hyC (h ▸ mem_insert_self _ _)
    show avr.testBit (16 * y) = true
    rw [havr]
    have h1 := hav y hyD hyC'
    simp only [bitS] at h1
    rw [h1, Bool.true_and]
    have hle : ¬ (16 * y ≤ 16 * z) ∨
        (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = false := by
      by_cases hm : (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = true
      · left
        intro hle
        obtain ⟨hcv, _⟩ := (hmbit y).mp hm
        have := hzle y (mem_filter.mpr ⟨hyD, hyC', hcv.2⟩)
        exact hyz (by omega)
      · right; simpa using hm
    rcases hle with h | h
    · rw [decide_eq_false h]; simp
    · rw [h]; rfl
  · intro j' hj'
    rw [uncS_child_M (lv0 p) hT s z hzadm avr, mem_filter] at hj'
    obtain ⟨hj'U, hnot⟩ := hj'
    obtain ⟨y, hyD, hyC, hcy⟩ := hcov j' hj'U
    refine ⟨y, hyD, fun hm => ?_, hcy⟩
    rcases mem_insert.mp hm with hyz | hmC
    · exact hnot ⟨hzW, by rw [← hyz]; exact hcy⟩
    · exact hyC hmC

/-- **`Sem` at level 0.** -/
theorem sem0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) (hT : TableOK9g X 0 p)
    (hW15 : X.W < 2 ^ 15) : Sem X (Cmp0 X p V) :=
  sem_mk_M (lv0 p) hT hW15 (Cmp0 X p V) (fun s hs => good0 hp hV hT s hs)
    (fun s j hs hj => hbr0 hp hV hT hW15 s j hs hj)

/-- **Delegation transfer at level 0.** -/
theorem hdel0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hT : TableOK9g X 0 p) (s h : St)
    (hs : Cmp0 X p V s) (he : stEq h s = true) :
    Cmp0 X p V { h with cu := X.cntF h.unc 0, nu := pcl 1024 h.unc 0 } := by
  unfold stEq at he
  simp only [Bool.and_eq_true, Nat.beq_eq] at he
  rcases he with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hav⟩, hfr⟩, hr⟩, hc3⟩, hch⟩, him⟩, hit⟩, hmp⟩, hmq⟩, hmf⟩
  obtain ⟨hwf, C, hch0, hCD, hCr, hfr0, him0, hit0, hmp0, hmq0, hmf0, hc30, hdis, hav0, hcov⟩ := hs
  have hu' : ∀ j, h.unc.testBit j = true → j ∈ Win p := by
    intro j hj; rw [hu] at hj; exact hwf.unc j hj
  have huncS : uncS p { h with cu := X.cntF h.unc 0, nu := pcl 1024 h.unc 0 } = uncS p s := by
    show (Win p).filter (fun j => h.unc.testBit j = true) = (Win p).filter (fun j => s.unc.testBit j = true)
    rw [hu]
  refine ⟨wf_of_unc_M (lv0 p) hT _ hu' rfl (pcl_nu_le p h.unc hu' 1024), C, ?_, hCD, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show h.ch = _; rw [hch]; exact hch0
  · show C.card + h.r = 8; rw [hr]; exact hCr
  · show h.fr = h.r; rw [hfr, hr]; exact hfr0
  · show h.im = 0; rw [him]; exact him0
  · show h.it = 0; rw [hit]; exact hit0
  · show h.mp = 0; rw [hmp]; exact hmp0
  · show h.mq = 0; rw [hmq]; exact hmq0
  · show h.mf = 0; rw [hmf]; exact hmf0
  · show h.c3 = 0; rw [hc3]; exact hc30
  · intro x hx; apply hdis x; rw [← hav]; exact hx
  · intro y hy hyC; show bitS h.av y = true; rw [hav]; exact hav0 y hy hyC
  · rw [huncS]; exact hcov

theorem hr0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (s : St) (hs : Cmp0 X p V s) (i : ℕ) :
    stEq (noH i) s = false := by
  obtain ⟨_, C, _, _, hCr, _⟩ := hs
  exact stEq_noH_false s (by omega) i

/-- **The root of the level-0 tree is in `Cmp0`.** -/
theorem hroot0 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp : 1 < p) (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 0 p) : Cmp0 X p V (root0 X) := by
  have hT' := hT
  obtain ⟨_, _, hfull, hadm, _⟩ := hT'
  rw [lv0] at hfull hadm
  have h1adm : 1 ∈ AdmC p p := by
    simp only [AdmC, Win, mem_filter, mem_Icc]
    refine ⟨⟨le_refl _, by omega⟩, ?_⟩
    rw [Nat.mod_eq_of_lt hp]; omega
  have hrow1 := row0 hT 1 h1adm
  have hU0 : (root0 X).unc = clr X.full
      (EightV4.compactOf ((Win p).filter (fun j => covM p j 1))) := by
    show clr X.full (X.row (sbit 1)).2.1 = _
    rw [sbit_eq9, mul_one, hrow1]
  have hu : ∀ j, (root0 X).unc.testBit j = true → j ∈ Win p := by
    intro j hj
    rw [hU0, testBit_clr9, hfull, EightV4.testBit_compactOf, Bool.and_eq_true] at hj
    exact of_decide_eq_true hj.1
  have hUS : uncS p (root0 X) = (Win p).filter (fun j => ¬ covM p j 1) := by
    ext j
    simp only [uncS, hU0, mem_filter, testBit_clr9, hfull, EightV4.testBit_compactOf, cc_bit,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨hjW, hj, hn⟩; exact ⟨hjW, fun h => hn ⟨hjW, h⟩⟩
    · rintro ⟨hjW, hn⟩; exact ⟨hjW, hjW, fun h => hn h.2⟩
  obtain ⟨v, hv, hred⟩ := hV.norm
  have h1D : 1 ∈ D0 p V := mem_image.mpr ⟨v, hv, hred⟩
  refine ⟨wf_of_unc_M (lv0 p) hT _ hu rfl (pcl_nu_le p _ hu 1024), {1}, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show sbit 1 = _; rw [sbit_eq9, spreadOf_single, mul_one]
  · exact Finset.singleton_subset_iff.mpr h1D
  · show ({1} : Finset ℕ).card + 7 = 8; simp
  · intro x hx hmem
    have hx' : bitS (clr X.adm (sbit 1)) x = true := hx
    rw [bitS_clr_sbit] at hx'
    have := (Bool.and_eq_true_iff.mp hx').2
    simp at hmem this
    exact this hmem
  · intro y hy hyC
    have hyC' : y ≠ 1 := fun h => hyC (mem_singleton.mpr h)
    show bitS (clr X.adm (sbit 1)) y = true
    rw [bitS_clr_sbit, hadm]
    simp only [bitS, tb_sp, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨d0_adm (by omega) hV hy, hyC'⟩
  · intro j hj
    rw [hUS, mem_filter] at hj
    obtain ⟨hjW, hnc⟩ := hj
    obtain ⟨y, hyD, hcy⟩ := d0_cover (by omega) hp2 hV j hjW
    refine ⟨y, hyD, fun hm => hnc ?_, hcy⟩
    rw [mem_singleton] at hm; rw [← hm]; exact hcy

end LRSpectrumFull.NineSound
