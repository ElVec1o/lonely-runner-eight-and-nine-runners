/-
# Nine runners, soundness part 4c: `Sem` at level 2 (`S2`)

`Cmp2` of part 3 is inductive against the level-2 branch step WITHOUT any added clause (the clause `c3 <= 6` is
re-derived for the child from the witnesses: `lvl2_three`).
* `lvl2_card_eq` (`fr = 0`): `I |_| T -> V \ C` by the witnesses is an injection onto `V \ C` (cardinality `|V \ C| <= r`);
* `lvl2_three`: `|T /\ 3Z| + |C /\ 3Z| <= 6`, and when it is `6` every multiple of 3 of `V \ C` lies over a forced item;
* `allowed2_core`: `V \ C` is inside the allowed mask;
* `hbr2`: the least coverer `z` of `V \ C` lies over one `p`-item (erased), one `3p`-item (erased) or over none
  (a free slot is used); the roles are exclusive because of the clause `not PM p c t`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Level1B

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

theorem row2 {X : Ctx} {p : ℕ} (hT : TableOK9g X 2 p) (x : ℕ) (hx : x ∈ AdmC (9 * p) p) :
    X.row (2 ^ (16 * x)) = (x, EightV4.compactOf ((Win (9 * p)).filter (fun j => covM (9 * p) j x)),
      EightV4.spreadOf ((AdmC (9 * p) p).filter (fun y => PM p x y)),
      EightV4.spreadOf ((AdmC (9 * p) p).filter (fun y => PM (3 * p) x y))) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrow, _, _⟩ := hT
  have := hrow x (by rw [lv2]; exact hx)
  rw [lv2] at this
  simpa using this

/-! ## Witness counting -/

theorem lvl2_card_eq {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V) (C I T : Finset ℕ)
    (hCV : C ⊆ V) (fr r : ℕ) (hcard : I.card + T.card + C.card + fr = 8) (hr : C.card + r = 8)
    (hwI : ∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ v ∉ C ∧ red (3 * p) v ∉ T)
    (hwT : ∀ t ∈ T, ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ C) (hf0 : fr = 0) :
    ∀ v ∈ V \ C, (∃ c ∈ I, red p v = c) ∨ (∃ t ∈ T, red (3 * p) v = t) := by
  choose! wI hwIV hwIr hwIC hwIT using hwI
  choose! wT hwTV hwTr hwTC using hwT
  have hiI : Set.InjOn wI I := by
    intro c hc c' hc' h
    have e1 := hwIr c hc
    have e2 := hwIr c' hc'
    rw [← e1, ← e2, h]
  have hiT : Set.InjOn wT T := by
    intro c hc c' hc' h
    have e1 := hwTr c hc
    have e2 := hwTr c' hc'
    rw [← e1, ← e2, h]
  have hdis : Disjoint (I.image wI) (T.image wT) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hxA
    obtain ⟨t, ht, hct⟩ := mem_image.mp hxB
    apply hwIT c hc
    rw [← hct, hwTr t ht]; exact ht
  have hsub : I.image wI ∪ T.image wT ⊆ V \ C := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp h
      exact mem_sdiff.mpr ⟨hwIV c hc, hwIC c hc⟩
    · obtain ⟨t, ht, rfl⟩ := mem_image.mp h
      exact mem_sdiff.mpr ⟨hwTV t ht, hwTC t ht⟩
  have hcu : (I.image wI ∪ T.image wT).card = I.card + T.card := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hiI,
      Finset.card_image_of_injOn hiT]
  have hle : (V \ C).card ≤ (I.image wI ∪ T.image wT).card := by
    rw [Finset.card_sdiff_of_subset hCV, hcu]
    have := hV.card
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  intro v hv
  rw [← heq] at hv
  rcases mem_union.mp hv with h | h
  · obtain ⟨c, hc, rfl⟩ := mem_image.mp h
    exact Or.inl ⟨c, hc, hwIr c hc⟩
  · obtain ⟨t, ht, rfl⟩ := mem_image.mp h
    exact Or.inr ⟨t, ht, hwTr t ht⟩

theorem lvl2_three {p : ℕ} {V : Finset ℕ} (hp : 0 < p) (hV : Good9 p V) (C T : Finset ℕ)
    (hCV : C ⊆ V) (hwT : ∀ t ∈ T, ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ C) :
    (T.filter (fun x => 3 ∣ x)).card + (C.filter (fun x => 3 ∣ x)).card ≤ 6 ∧
    (6 ≤ (T.filter (fun x => 3 ∣ x)).card + (C.filter (fun x => 3 ∣ x)).card →
      ∀ v ∈ V \ C, 3 ∣ v → ∃ t ∈ T, 3 ∣ t ∧ red (3 * p) v = t) := by
  choose! wT hwTV hwTr hwTC using hwT
  have hiT : Set.InjOn wT (T.filter (fun x => 3 ∣ x)) := by
    intro c hc c' hc' h
    have e1 := hwTr c (mem_filter.mp hc).1
    have e2 := hwTr c' (mem_filter.mp hc').1
    rw [← e1, ← e2, h]
  have hC3 : C.filter (fun x => 3 ∣ x) ⊆ V.filter (fun x => 3 ∣ x) := Finset.filter_subset_filter _ hCV
  have hsub : (T.filter (fun x => 3 ∣ x)).image wT ⊆ V.filter (fun x => 3 ∣ x) \ C.filter (fun x => 3 ∣ x) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
    obtain ⟨htT, ht3⟩ := mem_filter.mp ht
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hwTV t htT, ?_⟩, fun h => hwTC t htT (mem_filter.mp h).1⟩
    have := (red_dvd 3 (3 * p) (wT t) (by omega) (dvd_mul_right 3 p)).1
    rw [hwTr t htT] at this
    exact this ht3
  have hcardsub := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hiT, Finset.card_sdiff_of_subset hC3] at hcardsub
  have hside := hV.side
  have hc3le := Finset.card_le_card hC3
  refine ⟨by omega, ?_⟩
  intro hge v hv h3
  obtain ⟨hvV, hvC⟩ := mem_sdiff.mp hv
  have hle : (V.filter (fun x => 3 ∣ x) \ C.filter (fun x => 3 ∣ x)).card ≤
      ((T.filter (fun x => 3 ∣ x)).image wT).card := by
    rw [Finset.card_image_of_injOn hiT, Finset.card_sdiff_of_subset hC3]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hv' : v ∈ V.filter (fun x => 3 ∣ x) \ C.filter (fun x => 3 ∣ x) :=
    mem_sdiff.mpr ⟨mem_filter.mpr ⟨hvV, h3⟩, fun h => hvC (mem_filter.mp h).1⟩
  rw [← heq] at hv'
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hv'
  obtain ⟨htT, ht3⟩ := mem_filter.mp ht
  exact ⟨t, htT, ht3, hwTr t htT⟩

theorem pm_of_red {M x c : ℕ} (hM : 0 < M) (h : red M x = c) : PM M c x := by
  have := pm_red M x hM
  rw [h] at this
  exact pm_symm hM this

theorem allowed2_core {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (s : St) (C I T : Finset ℕ) (hCV : C ⊆ V)
    (hcard : I.card + T.card + C.card + s.fr = 8) (hr : C.card + s.r = 8)
    (hmp : s.mp = EightV4.spreadOf (liftSet (9 * p) p p I))
    (hmq : s.mq = EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c))))
    (hmf : s.mf = EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c))))
    (hc3 : s.c3 = (T.filter (fun c => 3 ∣ c)).card + (C.filter (fun c => 3 ∣ c)).card)
    (hav : ∀ y ∈ V, y ∉ C → bitS s.av y = true)
    (hwI : ∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ v ∉ C ∧ red (3 * p) v ∉ T)
    (hwT : ∀ t ∈ T, ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ C) :
    ∀ z ∈ V \ C, bitS (allowed X s) z = true ∧
      (s.fr = 0 → (∃ c ∈ I, PM p c z) ∨ ∃ t ∈ T, PM (3 * p) t z) := by
  have hp : 0 < p := by omega
  intro z hz
  obtain ⟨hzV, hzC⟩ := mem_sdiff.mp hz
  have hzadm : z ∈ AdmC (9 * p) p := hV.adm hzV
  have hzW : z ∈ Win (lvlMult 2 * p) := by rw [lv2]; exact (mem_filter.mp hzadm).1
  have hcnt := lvl2_card_eq hp2 hV C I T hCV s.fr s.r hcard hr hwI hwT
  have h2 : s.fr = 0 → (∃ c ∈ I, PM p c z) ∨ ∃ t ∈ T, PM (3 * p) t z := by
    intro h0
    rcases hcnt h0 z hz with ⟨c, hc, hrc⟩ | ⟨t, ht, hrt⟩
    · exact Or.inl ⟨c, hc, pm_of_red hp hrc⟩
    · exact Or.inr ⟨t, ht, pm_of_red (by omega) hrt⟩
  refine ⟨?_, h2⟩
  have hF3 : 6 ≤ s.c3 → 3 ∣ z → bitS s.mf z = true := by
    intro h6 h3
    rw [hc3] at h6
    obtain ⟨t, ht, ht3, hrt⟩ := (lvl2_three hp hV C T hCV hwT).2 h6 z hz h3
    rw [hmf, bitS, tb_sp]
    exact decide_eq_true (mem_filter.mpr ⟨hzadm, t, mem_filter.mpr ⟨ht, ht3⟩,
      pm_of_red (by omega) hrt⟩)
  by_cases hmfz : bitS s.mf z = true
  · exact allowed_intro_mf X s z hmfz (hav z hzV hzC)
  · refine allowed_intro X s z (hav z hzV hzC) ?_ ?_
    · by_cases h0 : s.fr = 0
      · right
        rcases hcnt h0 z hz with ⟨c, hc, hrc⟩ | ⟨t, ht, hrt⟩
        · left
          rw [hmp, bitS, tb_sp]
          exact decide_eq_true (mem_filter.mpr ⟨hzadm, c, hc, pm_of_red hp hrc⟩)
        · by_cases h3 : 3 ∣ t
          · exfalso
            apply hmfz
            rw [hmf, bitS, tb_sp]
            exact decide_eq_true (mem_filter.mpr ⟨hzadm, t, mem_filter.mpr ⟨ht, h3⟩,
              pm_of_red (by omega) hrt⟩)
          · right
            rw [hmq, bitS, tb_sp]
            exact decide_eq_true (mem_filter.mpr ⟨hzadm, t, mem_filter.mpr ⟨ht, h3⟩,
              pm_of_red (by omega) hrt⟩)
      · left; exact h0
    · rintro ⟨h5, hm3⟩
      rw [m3_bit (by norm_num) hT hzW] at hm3
      exact hmfz (hF3 (by omega) (of_decide_eq_true hm3))

theorem good2 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (s : St) (hs : Cmp2 X p V s) : WF X (9 * p) s ∧ Compl X (9 * p) s := by
  obtain ⟨hwf, C, I, T, hch, him, hit, hCV, hID, hTD, hcard, hr, hmp, hmq, hmf, hc3, h6, hdis, hav,
    hwI, hwT, hdisj, hcov⟩ := hs
  refine ⟨hwf, V \ C, ?_, ?_, ?_⟩
  · intro v hv
    refine ⟨(mem_filter.mp (hV.adm (mem_sdiff.mp hv).1)).1, ?_⟩
    exact (allowed2_core hp2 hV hT s C I T hCV hcard hr hmp hmq hmf hc3 hav hwI hwT v hv).1
  · rw [Finset.card_sdiff_of_subset hCV]
    have := hV.card
    omega
  · intro j hj
    obtain ⟨y, hyV, hyC, hcy⟩ := hcov j hj
    exact ⟨y, mem_sdiff.mpr ⟨hyV, hyC⟩, hcy⟩

theorem im_erase {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (I : Finset ℕ) (hID : I ⊆ D0 p V) (c0 z : ℕ) (hc0 : c0 ∈ I)
    (hpm : PM p c0 z) :
    clr (EightV4.spreadOf I) (Nat.land (EightV4.spreadOf ((AdmC (9 * p) p).filter
      (fun y => PM p z y))) X.lowp) = EightV4.spreadOf (I.erase c0) := by
  have hlowp : X.lowp = EightV4.spreadOf (Icc 1 ((p - 1) / 2)) := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hT; exact h
  have hLo : ∀ c, c ∈ Icc 1 ((p - 1) / 2) ↔ 1 ≤ c ∧ 2 * c < p := by
    intro c; simp only [mem_Icc]; omega
  rw [hlowp, spreadOf_land, spreadOf_clr,
    inter_erase (by omega) _ hLo I (fun c hc => d0_low hp2 hV (hID hc))
      (fun c hc => adm_mono' (by omega) (d0_adm (by omega) hV (hID hc))) hc0 hpm]

theorem it_erase {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (T : Finset ℕ) (hTD : T ⊆ D1 p V) (t0 z : ℕ) (ht0 : t0 ∈ T)
    (hpm : PM (3 * p) t0 z) :
    clr (EightV4.spreadOf T) (Nat.land (EightV4.spreadOf ((AdmC (9 * p) p).filter
      (fun y => PM (3 * p) z y))) X.lowT) = EightV4.spreadOf (T.erase t0) := by
  have hlowT : X.lowT = EightV4.spreadOf (Icc 1 (min ((lvlMult 2 * p) / 2) ((3 * p - 1) / 2))) := by
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hT; exact h
  have hLo : ∀ c, c ∈ Icc 1 (min ((lvlMult 2 * p) / 2) ((3 * p - 1) / 2)) ↔ 1 ≤ c ∧ 2 * c < 3 * p := by
    intro c; rw [lv2]; simp only [mem_Icc, le_min_iff]; omega
  rw [hlowT, spreadOf_land, spreadOf_clr,
    inter_erase (by omega) _ hLo T (fun c hc => d1_low hp2 hV (hTD hc))
      (fun c hc => adm_mono' (by omega) (d1_adm (by omega) hV (hTD hc))) ht0 hpm]

/-- **`Sem.branch` at level 2.** -/
theorem hbr2 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (hW15 : X.W < 2 ^ 15) (s : St) (j : ℕ) (hs : Cmp2 X p V s)
    (hj : bitC s.unc j = true) :
    ∃ e, (Nat.land (X.cbJ j) (allowed X s)).testBit e = true ∧
      ∀ avr, (∀ k, avr.testBit k = (s.av.testBit k &&
        !((Nat.land (X.cbJ j) (allowed X s)).testBit k && decide (k ≤ e)))) →
        Cmp2 X p V (childSt X s (2 ^ e) avr) := by
  have hp0 : 0 < p := by omega
  have hs' := hs
  obtain ⟨hwf, C, I, T, hch, him, hit, hCV, hID, hTD, hcard, hr, hmp, hmq, hmf, hc3, h6, hdis, hav,
    hwI, hwT, hdisj, hcov⟩ := hs'
  rw [bitC_eq9] at hj
  have hjW := hwf.unc j hj
  have hjU : j ∈ uncS (9 * p) s := mem_filter.mpr ⟨hjW, hj⟩
  obtain ⟨y0, hy0D, hy0C, hy0cov⟩ := hcov j hjU
  have hne : (V.filter (fun y => y ∉ C ∧ covM (9 * p) j y)).Nonempty :=
    ⟨y0, mem_filter.mpr ⟨hy0D, hy0C, hy0cov⟩⟩
  have hzY := Finset.min'_mem _ hne
  have hzle : ∀ y ∈ V.filter (fun y => y ∉ C ∧ covM (9 * p) j y),
      (V.filter (fun y => y ∉ C ∧ covM (9 * p) j y)).min' hne ≤ y :=
    fun y hy => Finset.min'_le _ y hy
  generalize (V.filter (fun y => y ∉ C ∧ covM (9 * p) j y)).min' hne = z at hzY hzle
  obtain ⟨hzV, hzC, hzcov⟩ := mem_filter.mp hzY |> fun h => (⟨h.1, h.2.1, h.2.2⟩ : _ ∧ _ ∧ _)
  have hzadm : z ∈ AdmC (9 * p) p := hV.adm hzV
  have hzW : z ∈ Win (9 * p) := (mem_filter.mp hzadm).1
  have hzS : z ∈ V \ C := mem_sdiff.mpr ⟨hzV, hzC⟩
  obtain ⟨hzal, hfr0⟩ := allowed2_core hp2 hV hT s C I T hCV hcard hr hmp hmq hmf hc3 hav hwI hwT z hzS
  have hr1 : 1 ≤ s.r := by
    have h1 := Finset.card_pos.mpr ⟨z, hzS⟩
    rw [Finset.card_sdiff_of_subset hCV] at h1
    have := hV.card
    omega
  have hmbit : ∀ y, (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = true ↔
      (cvr (9 * p) j y ∧ bitS (allowed X s) y = true) := by
    intro y
    rw [testBit_land9, cb_bit_M (lv2 p) hT hjW]
    simp [bitS]
  have hmz := (hmbit z).mpr ⟨⟨hzW, hzcov⟩, hzal⟩
  refine ⟨16 * z, hmz, ?_⟩
  intro avr havr
  obtain ⟨hch', hr', hav', hfr', hc3', him', hit', hmp', hmq', hmf'⟩ :=
    childSt_fields X s (2 ^ (16 * z)) avr z _ _ _ (row2 hT z hzadm)
  have eP : nz (Nat.land (2 ^ (16 * z)) s.mp) = decide (z ∈ liftSet (9 * p) p p I) := by
    rw [hmp]; exact nz_land_pow_sp z _
  have eQ : nz (Nat.land (2 ^ (16 * z)) s.mq) =
      decide (z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c))) := by
    rw [hmq]; exact nz_land_pow_sp z _
  have eF : nz (Nat.land (2 ^ (16 * z)) s.mf) =
      decide (z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c))) := by
    rw [hmf]; exact nz_land_pow_sp z _
  have e3 : nz (Nat.land (2 ^ (16 * z)) X.m3) = decide (3 ∣ z) := by
    rw [nz_land_pow]
    exact m3_bit (by norm_num) hT (by rw [lv2]; exact hzW)
  have hIlow : ∀ c ∈ I, 1 ≤ c ∧ 2 * c < p := fun c hc => d0_low hp2 hV (hID hc)
  have hTlow : ∀ t ∈ T, 1 ≤ t ∧ 2 * t < 3 * p := fun t ht => d1_low hp2 hV (hTD ht)
  have hredz : 2 * red (3 * p) z < 3 * p := by have := red_le (3 * p) z (by omega); omega
  have hexcl : ∀ c ∈ I, PM p c z → ∀ t ∈ T, ¬ PM (3 * p) t z := by
    intro c hc hpc t ht hpt
    have h1 : PM p t z := pm_mono (dvd_mul_left p 3) (by omega) hpt
    exact hdisj c hc t ht (pm_trans hp0 hpc (pm_symm hp0 h1))
  have hteq : ∀ t ∈ T, PM (3 * p) t z → t = red (3 * p) z := by
    intro t ht hpt
    exact pm_inj (hTlow t ht).2 hredz (pm_trans (by omega) hpt (pm_red (3 * p) z (by omega)))
  have hD : ∃ I' T' : Finset ℕ, I' ⊆ D0 p V ∧ T' ⊆ D1 p V ∧
      (childSt X s (2 ^ (16 * z)) avr).im = EightV4.spreadOf I' ∧
      (childSt X s (2 ^ (16 * z)) avr).it = EightV4.spreadOf T' ∧
      (childSt X s (2 ^ (16 * z)) avr).mp = EightV4.spreadOf (liftSet (9 * p) p p I') ∧
      (childSt X s (2 ^ (16 * z)) avr).mq =
        EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T'.filter (fun c => ¬ 3 ∣ c))) ∧
      (childSt X s (2 ^ (16 * z)) avr).mf =
        EightV4.spreadOf (liftSet (9 * p) p (3 * p) (T'.filter (fun c => 3 ∣ c))) ∧
      I'.card + T'.card + (childSt X s (2 ^ (16 * z)) avr).fr + 1 = I.card + T.card + s.fr ∧
      (T'.filter (fun c => 3 ∣ c)).card +
        (bif nz (Nat.land (2 ^ (16 * z)) s.mf) then 1 else 0) = (T.filter (fun c => 3 ∣ c)).card ∧
      (∀ c ∈ I', ∃ v ∈ V, red p v = c ∧ v ∉ insert z C ∧ red (3 * p) v ∉ T') ∧
      (∀ t ∈ T', ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ insert z C) ∧
      (∀ c ∈ I', ∀ t ∈ T', ¬ PM p c t) := by
    by_cases hP : z ∈ liftSet (9 * p) p p I
    · -- case A: over a p-item
      obtain ⟨_, c0, hc0, hpm0⟩ := mem_filter.mp hP
      have hzred : c0 = red p z := by
        have h1 := pm_trans hp0 hpm0 (pm_red p z hp0)
        have e := red_le p z hp0
        have := (hIlow c0 hc0).2
        exact pm_inj (by omega) (by omega) h1
      have hnT : ∀ t ∈ T, ¬ PM (3 * p) t z := hexcl c0 hc0 hpm0
      have hQ : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c)) := by
        intro h
        obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
        exact hnT t (mem_filter.mp ht).1 hpt
      have hF : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c)) := by
        intro h
        obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
        exact hnT t (mem_filter.mp ht).1 hpt
      have hfrA : (childSt X s (2 ^ (16 * z)) avr).fr = s.fr := by
        rw [hfr', eP, eQ, eF]; simp [hP, hQ, hF]
      refine ⟨I.erase c0, T, fun c hc => hID (mem_of_mem_erase hc), hTD, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [him', eP]
        simp only [hP, decide_true, cond_true]
        rw [him]; exact im_erase hp2 hV hT I hID c0 z hc0 hpm0
      · rw [hit', eQ, eF]
        simp only [hQ, hF, decide_false, Bool.or_self, cond_false]; exact hit
      · rw [hmp', eP]
        simp only [hP, decide_true, cond_true]
        rw [hmp, spreadOf_clr, lift_erase hp0 I (fun c hc => (hIlow c hc).2) c0 z hc0 hpm0]
      · rw [hmq', eQ]; simp only [hQ, decide_false, cond_false]; exact hmq
      · rw [hmf', eF]; simp only [hF, decide_false, cond_false]; exact hmf
      · rw [hfrA, Finset.card_erase_of_mem hc0]
        have := Finset.card_pos.mpr ⟨c0, hc0⟩
        omega
      · rw [eF]; simp [hF]
      · intro c hc
        obtain ⟨hcne, hcI⟩ := mem_erase.mp hc
        obtain ⟨v, hv, hvr, hvC, hvT⟩ := hwI c hcI
        refine ⟨v, hv, hvr, ?_, hvT⟩
        intro hin
        rcases mem_insert.mp hin with h | h
        · apply hcne
          have h2 : red p z = c := by rw [← h]; exact hvr
          rw [← h2]; exact hzred.symm
        · exact hvC h
      · intro t ht
        obtain ⟨v, hv, hvr, hvC⟩ := hwT t ht
        refine ⟨v, hv, hvr, ?_⟩
        intro hin
        rcases mem_insert.mp hin with h | h
        · exact hnT t ht (by rw [h] at hvr; exact pm_of_red (by omega) hvr)
        · exact hvC h
      · intro c hc t ht
        exact hdisj c (mem_of_mem_erase hc) t ht
    · by_cases hTz : ∃ t ∈ T, PM (3 * p) t z
      · -- case B: over a 3p-item
        obtain ⟨t0, ht0, hpm0⟩ := hTz
        have ht0red := hteq t0 ht0 hpm0
        have hfrB : (childSt X s (2 ^ (16 * z)) avr).fr = s.fr := by
          rw [hfr', eP, eQ, eF]
          by_cases h3 : 3 ∣ t0
          · have : z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c)) :=
              mem_filter.mpr ⟨hzadm, t0, mem_filter.mpr ⟨ht0, h3⟩, hpm0⟩
            simp [hP, this]
          · have : z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c)) :=
              mem_filter.mpr ⟨hzadm, t0, mem_filter.mpr ⟨ht0, h3⟩, hpm0⟩
            simp [hP, this]
        have hcommon : (∀ c ∈ I, ∃ v ∈ V, red p v = c ∧ v ∉ insert z C ∧ red (3 * p) v ∉ T.erase t0) ∧
            (∀ t ∈ T.erase t0, ∃ v ∈ V, red (3 * p) v = t ∧ v ∉ insert z C) := by
          constructor
          · intro c hc
            obtain ⟨v, hv, hvr, hvC, hvT⟩ := hwI c hc
            refine ⟨v, hv, hvr, ?_, fun h => hvT (mem_of_mem_erase h)⟩
            intro hin
            rcases mem_insert.mp hin with h | h
            · apply hvT
              rw [h, ← ht0red]; exact ht0
            · exact hvC h
          · intro t ht
            obtain ⟨hne', htT⟩ := mem_erase.mp ht
            obtain ⟨v, hv, hvr, hvC⟩ := hwT t htT
            refine ⟨v, hv, hvr, ?_⟩
            intro hin
            rcases mem_insert.mp hin with h | h
            · apply hne'
              rw [← hvr, h, ← ht0red]
            · exact hvC h
        have hnT0 : (T.erase t0).card + 1 = T.card := by
          rw [Finset.card_erase_of_mem ht0]
          have := Finset.card_pos.mpr ⟨t0, ht0⟩
          omega
        by_cases h3 : 3 ∣ t0
        · have hF : z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c)) :=
            mem_filter.mpr ⟨hzadm, t0, mem_filter.mpr ⟨ht0, h3⟩, hpm0⟩
          have hQ : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c)) := by
            intro h
            obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
            obtain ⟨htT, ht3⟩ := mem_filter.mp ht
            have : t = t0 := by rw [hteq t htT hpt, ← ht0red]
            exact ht3 (this ▸ h3)
          have ht0F : t0 ∈ T.filter (fun c => 3 ∣ c) := mem_filter.mpr ⟨ht0, h3⟩
          have hnotQ : t0 ∉ T.filter (fun c => ¬ 3 ∣ c) := fun h => (mem_filter.mp h).2 h3
          refine ⟨I, T.erase t0, hID, fun t ht => hTD (mem_of_mem_erase ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            hcommon.1, hcommon.2, fun c hc t ht => hdisj c hc t (mem_of_mem_erase ht)⟩
          · rw [him', eP]; simp only [hP, decide_false, cond_false]; exact him
          · rw [hit', eQ, eF]
            simp only [hQ, hF, decide_false, decide_true, Bool.false_or, cond_true]
            rw [hit]; exact it_erase hp2 hV hT T hTD t0 z ht0 hpm0
          · rw [hmp', eP]; simp only [hP, decide_false, cond_false]; exact hmp
          · rw [hmq', eQ]; simp only [hQ, decide_false, cond_false]
            rw [hmq, Finset.filter_erase, Finset.erase_eq_of_notMem hnotQ]
          · rw [hmf', eF]; simp only [hF, decide_true, cond_true]
            rw [hmf, spreadOf_clr, lift_erase (by omega : 0 < 3 * p) (T.filter (fun c => 3 ∣ c))
              (fun c hc => (hTlow c (mem_filter.mp hc).1).2) t0 z ht0F hpm0, Finset.filter_erase]
          · rw [hfrB]; omega
          · rw [eF]; simp only [hF, decide_true, cond_true]
            rw [Finset.filter_erase, Finset.card_erase_of_mem ht0F]
            have := Finset.card_pos.mpr ⟨t0, ht0F⟩
            omega
        · have hQ : z ∈ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c)) :=
            mem_filter.mpr ⟨hzadm, t0, mem_filter.mpr ⟨ht0, h3⟩, hpm0⟩
          have hF : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c)) := by
            intro h
            obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
            obtain ⟨htT, ht3⟩ := mem_filter.mp ht
            have : t = t0 := by rw [hteq t htT hpt, ← ht0red]
            exact h3 (this ▸ ht3)
          have ht0Q : t0 ∈ T.filter (fun c => ¬ 3 ∣ c) := mem_filter.mpr ⟨ht0, h3⟩
          have hnotF : t0 ∉ T.filter (fun c => 3 ∣ c) := fun h => h3 (mem_filter.mp h).2
          refine ⟨I, T.erase t0, hID, fun t ht => hTD (mem_of_mem_erase ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            hcommon.1, hcommon.2, fun c hc t ht => hdisj c hc t (mem_of_mem_erase ht)⟩
          · rw [him', eP]; simp only [hP, decide_false, cond_false]; exact him
          · rw [hit', eQ, eF]
            simp only [hQ, hF, decide_false, decide_true, Bool.true_or, Bool.or_false, cond_true]
            rw [hit]; exact it_erase hp2 hV hT T hTD t0 z ht0 hpm0
          · rw [hmp', eP]; simp only [hP, decide_false, cond_false]; exact hmp
          · rw [hmq', eQ]; simp only [hQ, decide_true, cond_true]
            rw [hmq, spreadOf_clr, lift_erase (by omega : 0 < 3 * p) (T.filter (fun c => ¬ 3 ∣ c))
              (fun c hc => (hTlow c (mem_filter.mp hc).1).2) t0 z ht0Q hpm0, Finset.filter_erase]
          · rw [hmf', eF]; simp only [hF, decide_false, cond_false]
            rw [hmf, Finset.filter_erase, Finset.erase_eq_of_notMem hnotF]
          · rw [hfrB]; omega
          · rw [eF]; simp only [hF, decide_false, cond_false, Nat.add_zero]
            rw [Finset.filter_erase, Finset.erase_eq_of_notMem hnotF]
      · -- case C: over no item
        have hnotLQ : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => ¬ 3 ∣ c)) := by
          intro h
          obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
          exact hTz ⟨t, (mem_filter.mp ht).1, hpt⟩
        have hnotLF : z ∉ liftSet (9 * p) p (3 * p) (T.filter (fun c => 3 ∣ c)) := by
          intro h
          obtain ⟨_, t, ht, hpt⟩ := mem_filter.mp h
          exact hTz ⟨t, (mem_filter.mp ht).1, hpt⟩
        have hnotI : ∀ c ∈ I, ¬ PM p c z := by
          intro c hc hpc
          exact hP (mem_filter.mpr ⟨hzadm, c, hc, hpc⟩)
        have hfrne : s.fr ≠ 0 := by
          intro h0
          rcases hfr0 h0 with ⟨c, hc, hpc⟩ | ⟨t, ht, hpt⟩
          · exact hnotI c hc hpc
          · exact hTz ⟨t, ht, hpt⟩
        have hfrC : (childSt X s (2 ^ (16 * z)) avr).fr = s.fr - 1 := by
          rw [hfr', eP, eQ, eF]; simp [hP, hnotLQ, hnotLF]
        refine ⟨I, T, hID, hTD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdisj⟩
        · rw [him', eP]; simp only [hP, decide_false, cond_false]; exact him
        · rw [hit', eQ, eF]; simp only [hnotLQ, hnotLF, decide_false, Bool.or_self, cond_false]; exact hit
        · rw [hmp', eP]; simp only [hP, decide_false, cond_false]; exact hmp
        · rw [hmq', eQ]; simp only [hnotLQ, decide_false, cond_false]; exact hmq
        · rw [hmf', eF]; simp only [hnotLF, decide_false, cond_false]; exact hmf
        · rw [hfrC]
          have : 1 ≤ s.fr := Nat.pos_of_ne_zero hfrne
          omega
        · rw [eF]; simp [hnotLF]
        · intro c hc
          obtain ⟨v, hv, hvr, hvC, hvT⟩ := hwI c hc
          refine ⟨v, hv, hvr, ?_, hvT⟩
          intro hin
          rcases mem_insert.mp hin with h | h
          · exact hnotI c hc (by rw [h] at hvr; exact pm_of_red hp0 hvr)
          · exact hvC h
        · intro t ht
          obtain ⟨v, hv, hvr, hvC⟩ := hwT t ht
          refine ⟨v, hv, hvr, ?_⟩
          intro hin
          rcases mem_insert.mp hin with h | h
          · exact hTz ⟨t, ht, by rw [h] at hvr; exact pm_of_red (by omega) hvr⟩
          · exact hvC h
  obtain ⟨I', T', hI'D, hT'D, hI'im, hT'it, hI'mp, hT'mq, hT'mf, hcardc, hΔ, hI'wit, hT'wit,
    hdisj'⟩ := hD
  have hCV' : insert z C ⊆ V := Finset.insert_subset_iff.mpr ⟨hzV, hCV⟩
  have hzCn : (insert z C).card = C.card + 1 := Finset.card_insert_of_notMem hzC
  have hc3child : (childSt X s (2 ^ (16 * z)) avr).c3 =
      (T'.filter (fun c => 3 ∣ c)).card + ((insert z C).filter (fun c => 3 ∣ c)).card := by
    rw [hc3', e3, hc3]
    generalize (bif nz (Nat.land (2 ^ (16 * z)) s.mf) then 1 else 0) = Δ at hΔ ⊢
    by_cases h3 : 3 ∣ z
    · have hn : z ∉ C.filter (fun x => 3 ∣ x) := fun h => hzC (mem_filter.mp h).1
      rw [Finset.filter_insert, if_pos h3, Finset.card_insert_of_notMem hn]
      simp only [h3, decide_true, cond_true]
      show Nat.sub (Nat.add _ 1) Δ = _
      simp only [Nat.sub_eq, Nat.add_eq]
      omega
    · rw [Finset.filter_insert, if_neg h3]
      simp only [h3, decide_false, cond_false]
      show Nat.sub (Nat.add _ 0) Δ = _
      simp only [Nat.sub_eq, Nat.add_eq]
      omega
  refine ⟨wf_child_M (lv2 p) hT hW15 s hwf z hzadm avr, insert z C, I', T', ?_, hI'im, hT'it, hCV',
    hI'D, hT'D, ?_, ?_, hI'mp, hT'mq, hT'mf, hc3child, ?_, ?_, ?_, hI'wit, hT'wit, hdisj', ?_⟩
  · rw [hch', hch, show Nat.lor (EightV4.spreadOf C) (2 ^ (16 * z)) =
        Nat.lor (2 ^ (16 * z)) (EightV4.spreadOf C) from Nat.lor_comm _ _, Finset.insert_eq,
      ← spreadOf_single z, spreadOf_lor]
  · omega
  · rw [hr', hzCn]
    show C.card + 1 + (s.r - 1) = 8
    omega
  · rw [hc3child]
    exact (lvl2_three hp0 hV (insert z C) T' hCV' hT'wit).1
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
  · intro y hyV hyC
    rw [hav']
    have hyC' : y ∉ C := fun h => hyC (mem_insert_of_mem h)
    have hyz : y ≠ z := fun h => hyC (h ▸ mem_insert_self _ _)
    show avr.testBit (16 * y) = true
    rw [havr]
    have h1 := hav y hyV hyC'
    simp only [bitS] at h1
    rw [h1, Bool.true_and]
    have hle : ¬ (16 * y ≤ 16 * z) ∨
        (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = false := by
      by_cases hm : (Nat.land (X.cbJ j) (allowed X s)).testBit (16 * y) = true
      · left
        intro hle
        obtain ⟨hcv, _⟩ := (hmbit y).mp hm
        have := hzle y (mem_filter.mpr ⟨hyV, hyC', hcv.2⟩)
        exact hyz (by omega)
      · right; simpa using hm
    rcases hle with h | h
    · rw [decide_eq_false h]; simp
    · rw [h]; rfl
  · intro j' hj'
    rw [uncS_child_M (lv2 p) hT s z hzadm avr, mem_filter] at hj'
    obtain ⟨hj'U, hnot⟩ := hj'
    obtain ⟨y, hyV, hyC, hcy⟩ := hcov j' hj'U
    refine ⟨y, hyV, fun hm => ?_, hcy⟩
    rcases mem_insert.mp hm with hyz | hmC
    · exact hnot ⟨hzW, by rw [← hyz]; exact hcy⟩
    · exact hyC hmC

/-- **`Sem` at level 2 (`S2`).** -/
theorem s2 {X : Ctx} {p : ℕ} {V : Finset ℕ} (hp2 : p % 2 = 1) (hV : Good9 p V)
    (hT : TableOK9g X 2 p) (hW15 : X.W < 2 ^ 15) : Sem X (Cmp2 X p V) :=
  sem_mk_M (lv2 p) hT hW15 (Cmp2 X p V) (fun s hs => good2 hp2 hV hT s hs)
    (fun s j hs hj => hbr2 hp2 hV hT hW15 s j hs hj)

end LRSpectrumFull.NineSound
