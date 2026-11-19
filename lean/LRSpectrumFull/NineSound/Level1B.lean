/-
# Nine runners, soundness part 4b: `Sem` at level 1 (`S1`)

`Cmp1` of part 3 (unchanged, no clause added) is inductive against the level-1 branch step.
* `lvl1_fr0`: when `fr = 0`, the canonical completion `D1 \ C` lies entirely over unsatisfied items (witness counting:
  `c -> red_{3p}(witness c)` is an injection `I -> D1 \ C` with `|D1 \ C| <= r = |I|`);
* `allowed1_core`: `D1 \ C` is inside the allowed mask (free slots, item lifts, and the F-removal when `c3 >= 6`, where
  `C /\ 3Z = D1 /\ 3Z` by `d1_three`);
* `hbr1`: the least coverer `z` of `D1 \ C`; either `z` lies over the item `c0 = red_p z` (item erased, `fr` kept)
  or over none (`fr` decreases); `s1 : Sem X (Cmp1 X p V)`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Pm9

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

theorem d0_low {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V) {c : ℕ} (hc : c ∈ D0 p V) :
    1 ≤ c ∧ 2 * c < p := by
  have h := d0_adm (by omega) hV hc
  simp only [AdmC, Win, mem_filter, mem_Icc] at h
  omega

theorem d1_low {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V) {c : ℕ} (hc : c ∈ D1 p V) :
    1 ≤ c ∧ 2 * c < 3 * p := by
  have h := d1_adm (by omega) hV hc
  simp only [AdmC, Win, mem_filter, mem_Icc] at h
  omega

theorem m3_bit {X : Ctx} {i p : ℕ} (hi : i ≠ 0) (hT : TableOK9g X i p) {v : ℕ}
    (hv : v ∈ Win (lvlMult i * p)) : bitS X.m3 v = decide (3 ∣ v) := by
  obtain ⟨_, _, _, _, hm3, _⟩ := hT
  rw [if_neg hi] at hm3
  rw [hm3, bitS, tb_sp]
  exact decide_eq_decide.mpr (by simp [mem_filter, hv, Nat.dvd_iff_mod_eq_zero])

theorem row1 {X : Ctx} {p : ℕ} (hT : TableOK9g X 1 p) (x : ℕ) (hx : x ∈ AdmC (3 * p) p) :
    X.row (2 ^ (16 * x)) = (x, EightV4.compactOf ((Win (3 * p)).filter (fun j => covM (3 * p) j x)),
      EightV4.spreadOf ((AdmC (3 * p) p).filter (fun y => PM p x y)), 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrow, _, _⟩ := hT
  have := hrow x (by rw [lv1]; exact hx)
  rw [lv1] at this
  simpa using this

theorem inter_erase {A : Finset ℕ} {m z t0 : ℕ} (hm : 0 < m) (Lo : Finset ℕ)
    (hLo : ∀ c, c ∈ Lo ↔ 1 ≤ c ∧ 2 * c < m) (I : Finset ℕ) (hI : ∀ c ∈ I, 1 ≤ c ∧ 2 * c < m)
    (hIA : ∀ c ∈ I, c ∈ A) (ht0 : t0 ∈ I) (hpm : PM m t0 z) :
    I \ ((A.filter (fun y => PM m z y)) ∩ Lo) = I.erase t0 := by
  ext c
  simp only [mem_sdiff, mem_inter, mem_filter, mem_erase]
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨?_, hc⟩
    intro hct
    apply hn
    rw [hct]
    exact ⟨⟨hIA t0 ht0, pm_symm hm hpm⟩, (hLo t0).mpr (hI t0 ht0)⟩
  · rintro ⟨hne, hc⟩
    refine ⟨hc, ?_⟩
    rintro ⟨⟨_, hzc⟩, _⟩
    exact hne (pm_inj (hI c hc).2 (hI t0 ht0).2 (pm_trans hm (pm_symm hm hzc) (pm_symm hm hpm)))

/-! ## Witness counting -/

theorem lvl1_inj {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (C I : Finset ℕ)
    (hwit : ∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ red (3 * p) v ∉ C) :
    ∃ f : ℕ → ℕ, (∀ c ∈ I, f c ∈ D1 p V ∧ f c ∉ C ∧ PM p c (f c)) ∧ Set.InjOn f I := by
  have hp : 0 < p := by omega
  choose! w hwV hwr hwn using hwit
  refine ⟨fun c => red (3 * p) (w c), ?_, ?_⟩
  · intro c hc
    refine ⟨mem_image_of_mem _ (hwV c hc), hwn c hc, ?_⟩
    have h1 := pm_red p (red (3 * p) (w c)) hp
    rw [red_red3 hp hp2, hwr c hc] at h1
    exact pm_symm hp h1
  · intro c hc c' hc' h
    have e1 : c = red p (red (3 * p) (w c)) := by rw [red_red3 hp hp2, hwr c hc]
    have e2 : c' = red p (red (3 * p) (w c')) := by rw [red_red3 hp hp2, hwr c' hc']
    simp only at h
    rw [e1, e2, h]

theorem lvl1_fr0 {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V) (C I : Finset ℕ)
    (hCD : C ⊆ D1 p V) (fr r : ℕ) (hcard : I.card + C.card + fr = 8) (hr : C.card + r = 8)
    (hwit : ∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ red (3 * p) v ∉ C) (hf0 : fr = 0) :
    ∀ z ∈ D1 p V \ C, ∃ c ∈ I, PM p c z := by
  obtain ⟨f, hf, hinj⟩ := lvl1_inj (V := V) hp2 C I hwit
  have hsub : I.image f ⊆ D1 p V \ C := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hy
    exact mem_sdiff.mpr ⟨(hf c hc).1, (hf c hc).2.1⟩
  have hcardI : (I.image f).card = I.card := Finset.card_image_of_injOn hinj
  have hle : (D1 p V \ C).card ≤ (I.image f).card := by
    rw [Finset.card_sdiff_of_subset hCD, hcardI]
    have := d1_card hV
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  intro z hz
  rw [← heq] at hz
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hz
  exact ⟨c, hc, (hf c hc).2.2⟩

theorem allowed1_core {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 1 p) (s : St) (C I : Finset ℕ) (hCD : C ⊆ D1 p V)
    (hcard : I.card + C.card + s.fr = 8) (hr : C.card + s.r = 8)
    (hmp : s.mp = EightV4.spreadOf (liftSet (3 * p) p p I))
    (hc3 : s.c3 = (C.filter (fun x => 3 ∣ x)).card)
    (hav : ∀ y ∈ D1 p V, y ∉ C → bitS s.av y = true)
    (hwit : ∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ red (3 * p) v ∉ C) :
    ∀ z ∈ D1 p V \ C, bitS (allowed X s) z = true ∧ (s.fr = 0 → ∃ c ∈ I, PM p c z) := by
  intro z hz
  obtain ⟨hzD, hzC⟩ := mem_sdiff.mp hz
  have hfr := lvl1_fr0 hp2 hV C I hCD s.fr s.r hcard hr hwit
  refine ⟨allowed_intro X s z (hav z hzD hzC) ?_ ?_, fun h => hfr h z hz⟩
  · by_cases h0 : s.fr = 0
    · right; left
      obtain ⟨c, hc, hpc⟩ := hfr h0 z hz
      rw [hmp, bitS, tb_sp]
      exact decide_eq_true (mem_filter.mpr ⟨d1_adm (by omega) hV hzD, c, hc, hpc⟩)
    · left; exact h0
  · rintro ⟨h5, hm3⟩
    rw [hc3] at h5
    have hzW : z ∈ Win (lvlMult 1 * p) := by
      rw [lv1]; exact (mem_filter.mp (d1_adm (by omega) hV hzD)).1
    rw [m3_bit (by norm_num) hT hzW] at hm3
    have h3 : 3 ∣ z := of_decide_eq_true hm3
    have hsub : C.filter (fun x => 3 ∣ x) ⊆ (D1 p V).filter (fun x => 3 ∣ x) :=
      Finset.filter_subset_filter _ hCD
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have := d1_three (by omega : 0 < p) hV
      omega)
    have : z ∈ (D1 p V).filter (fun x => 3 ∣ x) := mem_filter.mpr ⟨hzD, h3⟩
    rw [← heq] at this
    exact hzC (mem_filter.mp this).1

theorem good1 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 1 p) (s : St) (hs : Cmp1 X p V s) : WF X (3 * p) s ∧ Compl X (3 * p) s := by
  obtain ⟨hwf, C, I, hch, him, hCD, hID, hcard, hr, hit, hmq, hmf, hmp, hc3, hdis, hav, hwit, hdisj,
    hcov⟩ := hs
  refine ⟨hwf, D1 p V \ C, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvD, hvC⟩ := mem_sdiff.mp hv
    refine ⟨(mem_filter.mp (d1_adm (by omega) hV hvD)).1, ?_⟩
    exact (allowed1_core hp2 hV hT s C I hCD hcard hr hmp hc3 hav hwit v hv).1
  · rw [Finset.card_sdiff_of_subset hCD]
    have := d1_card hV
    omega
  · intro j hj
    obtain ⟨y, hyD, hyC, hcy⟩ := hcov j hj
    exact ⟨y, mem_sdiff.mpr ⟨hyD, hyC⟩, hcy⟩

/-- **`Sem.branch` at level 1.** -/
theorem hbr1 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 1 p) (hW15 : X.W < 2 ^ 15) (s : St) (j : ℕ) (hs : Cmp1 X p V s)
    (hj : bitC s.unc j = true) :
    ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
      ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
        !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
        Cmp1 X p V (childSt X s (2 ^ e) avr) := by
  have hp0 : 0 < p := by omega
  have hs' := hs
  obtain ⟨hwf, C, I, hch, him, hCD, hID, hcard, hr, hit, hmq, hmf, hmp, hc3, hdis, hav, hwit, hdisj,
    hcov⟩ := hs'
  rw [bitC_eq9] at hj
  have hjW := hwf.unc j hj
  have hjU : j ∈ uncS (3 * p) s := mem_filter.mpr ⟨hjW, hj⟩
  obtain ⟨y0, hy0D, hy0C, hy0cov⟩ := hcov j hjU
  have hne : ((D1 p V).filter (fun y => y ∉ C ∧ covM (3 * p) j y)).Nonempty :=
    ⟨y0, mem_filter.mpr ⟨hy0D, hy0C, hy0cov⟩⟩
  have hzY := Finset.min'_mem _ hne
  have hzle : ∀ y ∈ (D1 p V).filter (fun y => y ∉ C ∧ covM (3 * p) j y),
      ((D1 p V).filter (fun y => y ∉ C ∧ covM (3 * p) j y)).min' hne ≤ y :=
    fun y hy => Finset.min'_le _ y hy
  generalize ((D1 p V).filter (fun y => y ∉ C ∧ covM (3 * p) j y)).min' hne = z at hzY hzle
  obtain ⟨hzD, hzC, hzcov⟩ := mem_filter.mp hzY |> fun h => (⟨h.1, h.2.1, h.2.2⟩ : _ ∧ _ ∧ _)
  have hzadm : z ∈ AdmC (3 * p) p := d1_adm hp0 hV hzD
  have hzW : z ∈ Win (3 * p) := (mem_filter.mp hzadm).1
  have hzS : z ∈ D1 p V \ C := mem_sdiff.mpr ⟨hzD, hzC⟩
  obtain ⟨hzal, hfr0⟩ := allowed1_core hp2 hV hT s C I hCD hcard hr hmp hc3 hav hwit z hzS
  have hr1 : 1 ≤ s.r := by
    have h1 := Finset.card_pos.mpr ⟨z, hzS⟩
    rw [Finset.card_sdiff_of_subset hCD] at h1
    have := d1_card hV
    omega
  have hmbit : ∀ y, (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = true ↔
      (cvr (3 * p) j y ∧ bitS (allowed X s) y = true) := by
    intro y
    rw [testBit_land9, cb_bit_M (lv1 p) hT hjW]
    simp [bitS]
  have hmz := (hmbit z).mpr ⟨⟨hzW, hzcov⟩, hzal⟩
  refine ⟨16 * z, hmz, ?_⟩
  intro avr havr
  obtain ⟨hch', hr', hav', hfr', hc3', him', hit', hmp', hmq', hmf'⟩ :=
    childSt_fields X s (2 ^ (16 * z)) avr z _ _ _ (row1 hT z hzadm)
  have hlowp : X.lowp = EightV4.spreadOf (Icc 1 ((p - 1) / 2)) := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hT; exact h
  have eQ : nz (Nat.land (2 ^ (16 * z)) s.mq) = false := by rw [hmq]; exact nz_land_zero _
  have eF : nz (Nat.land (2 ^ (16 * z)) s.mf) = false := by rw [hmf]; exact nz_land_zero _
  have eP : nz (Nat.land (2 ^ (16 * z)) s.mp) = decide (z ∈ liftSet (3 * p) p p I) := by
    rw [hmp]; exact nz_land_pow_sp z _
  have e3 : nz (Nat.land (2 ^ (16 * z)) X.m3) = decide (3 ∣ z) := by
    rw [nz_land_pow]
    exact m3_bit (by norm_num) hT (by rw [lv1]; exact hzW)
  have hlow : ∀ c, c ∈ Icc 1 ((p - 1) / 2) ↔ 1 ≤ c ∧ 2 * c < p := by
    intro c; simp only [mem_Icc]; omega
  have hIlow : ∀ c ∈ I, 1 ≤ c ∧ 2 * c < p := fun c hc => d0_low hp2 hV (hID hc)
  -- the item data of the child
  have hI' : ∃ I' : Finset ℕ, I' ⊆ D0 p V ∧
      (childSt X s (2 ^ (16 * z)) avr).im = EightV4.spreadOf I' ∧
      (childSt X s (2 ^ (16 * z)) avr).mp = EightV4.spreadOf (liftSet (3 * p) p p I') ∧
      I'.card + (childSt X s (2 ^ (16 * z)) avr).fr + 1 = I.card + s.fr ∧
      (∀ c ∈ I', ∃ v ∈ V, red p v = c ∧ red (3 * p) v ∉ insert z C) ∧
      (∀ c ∈ I', ∀ y ∈ insert z C, ¬ PM p c y) := by
    by_cases hP : z ∈ liftSet (3 * p) p p I
    · obtain ⟨_, c0, hc0, hpm0⟩ := mem_filter.mp hP
      have hzred : c0 = red p z := by
        have h1 := pm_trans hp0 hpm0 (pm_red p z hp0)
        have e := red_le p z hp0
        have := (hIlow c0 hc0).2
        exact pm_inj (by omega) (by omega) h1
      refine ⟨I.erase c0, fun c hc => hID (mem_of_mem_erase hc), ?_, ?_, ?_, ?_, ?_⟩
      · rw [him', eP]
        simp only [hP, decide_true, cond_true]
        rw [him, hlowp, spreadOf_land, spreadOf_clr,
          inter_erase hp0 _ hlow I hIlow (fun c hc => adm_mono (d0_adm hp0 hV (hID hc))) hc0 hpm0]
      · rw [hmp', eP]
        simp only [hP, decide_true, cond_true]
        rw [hmp, spreadOf_clr, lift_erase hp0 I (fun c hc => (hIlow c hc).2) c0 z hc0 hpm0]
      · rw [hfr', eP, eQ, eF]
        simp only [hP, decide_true, Bool.true_or, cond_true]
        have : c0 ∈ I := hc0
        rw [Finset.card_erase_of_mem hc0]
        have := Finset.card_pos.mpr ⟨c0, hc0⟩
        omega
      · intro c hc
        obtain ⟨hcne, hcI⟩ := mem_erase.mp hc
        obtain ⟨v, hv, hvr, hvn⟩ := hwit c hcI
        refine ⟨v, hv, hvr, ?_⟩
        intro hin
        rcases mem_insert.mp hin with h | h
        · apply hcne
          have h2 : red p z = c := by rw [← h, red_red3 hp0 hp2, hvr]
          rw [← h2]; exact hzred.symm
        · exact hvn h
      · intro c hc y hy
        obtain ⟨hcne, hcI⟩ := mem_erase.mp hc
        rcases mem_insert.mp hy with h | h
        · rw [h]
          intro hpc
          exact hcne (pm_inj (hIlow c hcI).2 (hIlow c0 hc0).2
            (pm_trans hp0 hpc (pm_symm hp0 hpm0)))
        · exact hdisj c hcI y h
    · have hnp : ∀ c ∈ I, ¬ PM p c z := by
        intro c hc hpc
        exact hP (mem_filter.mpr ⟨hzadm, c, hc, hpc⟩)
      have hfrne : s.fr ≠ 0 := by
        intro h0
        obtain ⟨c, hc, hpc⟩ := hfr0 h0
        exact hnp c hc hpc
      refine ⟨I, hID, ?_, ?_, ?_, ?_, ?_⟩
      · rw [him', eP]; simp only [hP, decide_false, cond_false]; exact him
      · rw [hmp', eP]; simp only [hP, decide_false, cond_false]; exact hmp
      · rw [hfr', eP, eQ, eF]
        simp only [hP, decide_false, Bool.or_self, cond_false]
        have : 1 ≤ s.fr := Nat.pos_of_ne_zero hfrne
        show I.card + (s.fr - 1) + 1 = I.card + s.fr
        omega
      · intro c hc
        obtain ⟨v, hv, hvr, hvn⟩ := hwit c hc
        refine ⟨v, hv, hvr, ?_⟩
        intro hin
        rcases mem_insert.mp hin with h | h
        · apply hnp c hc
          have h2 : red p z = c := by rw [← h, red_red3 hp0 hp2, hvr]
          have := pm_red p z hp0
          rw [h2] at this
          exact pm_symm hp0 this
        · exact hvn h
      · intro c hc y hy
        rcases mem_insert.mp hy with h | h
        · rw [h]; exact hnp c hc
        · exact hdisj c hc y h
  obtain ⟨I', hI'D, hI'im, hI'mp, hI'card, hI'wit, hI'disj⟩ := hI'
  have hzC' : z ∉ C := hzC
  refine ⟨wf_child_M (lv1 p) hT hW15 s hwf z hzadm avr, insert z C, I', ?_, hI'im, ?_, hI'D, ?_, ?_,
    ?_, ?_, ?_, hI'mp, ?_, ?_, ?_, hI'wit, hI'disj, ?_⟩
  · rw [hch', hch, show Nat.lor (EightV4.spreadOf C) (2 ^ (16 * z)) =
        Nat.lor (2 ^ (16 * z)) (EightV4.spreadOf C) from Nat.lor_comm _ _, Finset.insert_eq,
      ← spreadOf_single z, spreadOf_lor]
  · exact Finset.insert_subset_iff.mpr ⟨hzD, hCD⟩
  · rw [Finset.card_insert_of_notMem hzC]
    omega
  · rw [Finset.card_insert_of_notMem hzC, hr']
    show C.card + 1 + (s.r - 1) = 8
    omega
  · rw [hit', eQ, eF]; simpa using hit
  · rw [hmq', eQ]; simpa using hmq
  · rw [hmf', eF]; simpa using hmf
  · rw [hc3', eF, e3, hc3, Finset.filter_insert]
    by_cases h3 : 3 ∣ z
    · have hn : z ∉ C.filter (fun x => 3 ∣ x) := fun h => hzC (mem_filter.mp h).1
      simp only [h3, decide_true, if_true, cond_true, cond_false, Finset.card_insert_of_notMem hn]
      rfl
    · simp only [h3, decide_false, if_false, cond_false]
      rfl
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
    rw [uncS_child_M (lv1 p) hT s z hzadm avr, mem_filter] at hj'
    obtain ⟨hj'U, hnot⟩ := hj'
    obtain ⟨y, hyD, hyC, hcy⟩ := hcov j' hj'U
    refine ⟨y, hyD, fun hm => ?_, hcy⟩
    rcases mem_insert.mp hm with hyz | hmC
    · exact hnot ⟨hzW, by rw [← hyz]; exact hcy⟩
    · exact hyC hmC

/-- **`Sem` at level 1 (`S1`).** -/
theorem s1 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 1 p) (hW15 : X.W < 2 ^ 15) : Sem X (Cmp1 X p V) :=
  sem_mk_M (lv1 p) hT hW15 (Cmp1 X p V) (fun s hs => good1 hp2 hV hT s hs)
    (fun s j hs hj => hbr1 hp2 hV hT hW15 s j hs hj)

end LRSpectrumFull.NineSound
