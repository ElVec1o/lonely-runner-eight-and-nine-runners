/-
# Nine runners, soundness part 4a: the `+-` congruence calculus and mask glue for the level-1/2 role analysis

`PM m c y` (`y = +-c mod m`) is symmetric and transitive; two classes `c, c'` with `2c, 2c' < m` that are `+-`
congruent are equal; the fold `red M x` satisfies `PM M x (red M x)`; `red p (red (3p) x) = red p x` for odd `p`;
erasing the item `t0` over a pick `z` from a lifted item set (`lift_erase`); bit glue `nz (land (2^k) x)`;
the fields of `childSt` and the introduction rules of the `allowed` mask.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Level2

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

theorem pm_modeq (m c y : ℕ) (hm : 0 < m) : PM m c y ↔ (y ≡ c [MOD m] ∨ y + c ≡ 0 [MOD m]) := by
  unfold PM Nat.ModEq
  rw [Nat.zero_mod]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [Nat.add_mod, h, Nat.mod_self]
  · rintro (h | h)
    · exact Or.inl h
    · by_cases heq : y % m = c % m
      · exact Or.inl heq
      · right
        have ha := Nat.mod_lt y hm
        have hb := Nat.mod_lt c hm
        rw [Nat.add_mod] at h
        by_cases hlt : y % m + c % m < m
        · rw [Nat.mod_eq_of_lt hlt] at h; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega

theorem pm_symm {m c y : ℕ} (hm : 0 < m) (h : PM m c y) : PM m y c := by
  rw [pm_modeq m _ _ hm] at h ⊢
  rcases h with h | h
  · exact Or.inl h.symm
  · right; rwa [Nat.add_comm]

theorem pm_trans {m a b c : ℕ} (hm : 0 < m) (h1 : PM m a b) (h2 : PM m b c) : PM m a c := by
  rw [pm_modeq m _ _ hm] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h2.trans h1)
  · right; exact (Nat.ModEq.add_left c h1.symm).trans h2
  · right; exact (Nat.ModEq.add_right a h2).trans h1
  · left
    have h3 : c + b ≡ a + b [MOD m] := h2.trans (by rw [Nat.add_comm a b]; exact h1.symm)
    exact Nat.ModEq.add_right_cancel' b h3

theorem pm_mono {g m c y : ℕ} (hg : g ∣ m) (hm : 0 < m) (h : PM m c y) : PM g c y := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hm
  rw [pm_modeq m _ _ hm] at h
  rw [pm_modeq g _ _ hg0]
  rcases h with h | h
  · exact Or.inl (Nat.ModEq.of_dvd hg h)
  · exact Or.inr (Nat.ModEq.of_dvd hg h)

theorem pm_red (M x : ℕ) (hM : 0 < M) : PM M x (red M x) := by
  unfold PM red
  have ha := Nat.mod_lt x hM
  by_cases hle : x % M ≤ M - x % M
  · rw [min_eq_left hle]; left; rw [Nat.mod_mod]
  · rw [min_eq_right (by omega)]; right
    rw [Nat.mod_eq_of_lt (by omega : M - x % M < M)]; omega

theorem red_le (M x : ℕ) (hM : 0 < M) : 2 * red M x ≤ M := by
  unfold red
  have := Nat.mod_lt x hM
  omega

theorem pm_inj {m c c' : ℕ} (hc : 2 * c < m) (hc' : 2 * c' < m) (h : PM m c c') : c = c' := by
  unfold PM at h
  rw [Nat.mod_eq_of_lt (by omega : c' < m), Nat.mod_eq_of_lt (by omega : c < m)] at h
  omega

theorem red_red3 {p : ℕ} (hp : 0 < p) (hp2 : p % 2 = 1) (x : ℕ) :
    red p (red (3 * p) x) = red p x := by
  have h1 : PM p (red (3 * p) x) (red p (red (3 * p) x)) := pm_red p _ hp
  have h2 : PM (3 * p) x (red (3 * p) x) := pm_red (3 * p) x (by omega)
  have h3 : PM p x (red p x) := pm_red p x hp
  have h2' : PM p x (red (3 * p) x) := pm_mono (dvd_mul_left p 3) (by omega) h2
  have h4 := pm_trans hp (pm_symm hp h1) (pm_trans hp (pm_symm hp h2') h3)
  have e1 := red_le p (red (3 * p) x) hp
  have e2 := red_le p x hp
  exact pm_inj (by omega) (by omega) h4

/-- erasing the item `t0` that lies over the pick `z` from a lifted item set -/
theorem lift_erase {M p m : ℕ} (hm : 0 < m) (U : Finset ℕ) (hU : ∀ c ∈ U, 2 * c < m) (t0 z : ℕ)
    (ht0 : t0 ∈ U) (hpm : PM m t0 z) :
    liftSet M p m U \ ((AdmC M p).filter (fun y => PM m z y)) = liftSet M p m (U.erase t0) := by
  ext y
  simp only [liftSet, mem_sdiff, mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨hy, c, hc, hpc⟩, hn⟩
    refine ⟨hy, c, ⟨?_, hc⟩, hpc⟩
    intro h
    rw [h] at hpc
    exact hn ⟨hy, pm_trans hm (pm_symm hm hpm) hpc⟩
  · rintro ⟨hy, c, ⟨hne, hc⟩, hpc⟩
    refine ⟨⟨hy, c, hc, hpc⟩, ?_⟩
    rintro ⟨_, hzy⟩
    have hcz : PM m c z := pm_trans hm hpc (pm_symm hm hzy)
    have hct : PM m c t0 := pm_trans hm hcz (pm_symm hm hpm)
    exact hne (pm_inj (hU c hc) (hU t0 ht0) hct)

/-- the lifted items over a pick `z` that is not over any item: nothing to erase -/
theorem not_lift_of_not_pm {M p m : ℕ} (hm : 0 < m) (U : Finset ℕ) (z : ℕ)
    (h : ∀ c ∈ U, ¬ PM m c z) : z ∉ liftSet M p m U := by
  intro hz
  simp only [liftSet, mem_filter] at hz
  obtain ⟨_, c, hc, hpc⟩ := hz
  exact h c hc hpc

/-! ## Bit glue -/

theorem testBit_lor9 (a b i : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_lor a b i

theorem nz_land_pow (k x : ℕ) : nz (Nat.land (2 ^ k) x) = x.testBit k := by
  by_cases h : x.testBit k = true
  · have h1 : (Nat.land (2 ^ k) x).testBit k = true := by
      rw [testBit_land9, Nat.testBit_two_pow]; simp [h]
    have hne : Nat.land (2 ^ k) x ≠ 0 := fun h0 => by rw [h0] at h1; simp at h1
    rw [h]; unfold nz; rw [beq_zero_false _ hne]; rfl
  · have h' : x.testBit k = false := by simpa using h
    have h0 : Nat.land (2 ^ k) x = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_land9, Nat.testBit_two_pow]
      by_cases hik : k = i
      · subst hik; simp [h']
      · simp [hik]
    rw [h']; unfold nz; rw [h0]; rfl

theorem nz_land_pow_sp (z : ℕ) (S : Finset ℕ) :
    nz (Nat.land (2 ^ (16 * z)) (EightV4.spreadOf S)) = decide (z ∈ S) := by
  rw [nz_land_pow, tb_sp]

theorem nz_land_zero (b : ℕ) : nz (Nat.land b 0) = false := by
  unfold nz; simp [Nat.land_eq]

/-- the fields of the child state -/
theorem childSt_fields (X : Ctx) (s : St) (b avr c cc pc tc : ℕ) (h : X.row b = (c, cc, pc, tc)) :
    (childSt X s b avr).ch = Nat.lor s.ch b ∧ (childSt X s b avr).r = Nat.sub s.r 1 ∧
    (childSt X s b avr).av = avr ∧
    (childSt X s b avr).fr = (bif nz (Nat.land b s.mp) || nz (Nat.land b s.mq) || nz (Nat.land b s.mf)
        then s.fr else Nat.sub s.fr 1) ∧
    (childSt X s b avr).c3 = Nat.sub (Nat.add s.c3 (bif nz (Nat.land b X.m3) then 1 else 0))
        (bif nz (Nat.land b s.mf) then 1 else 0) ∧
    (childSt X s b avr).im = (bif nz (Nat.land b s.mp) then clr s.im (Nat.land pc X.lowp) else s.im) ∧
    (childSt X s b avr).it = (bif nz (Nat.land b s.mq) || nz (Nat.land b s.mf)
        then clr s.it (Nat.land tc X.lowT) else s.it) ∧
    (childSt X s b avr).mp = (bif nz (Nat.land b s.mp) then clr s.mp pc else s.mp) ∧
    (childSt X s b avr).mq = (bif nz (Nat.land b s.mq) then clr s.mq tc else s.mq) ∧
    (childSt X s b avr).mf = (bif nz (Nat.land b s.mf) then clr s.mf tc else s.mf) := by
  unfold childSt
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- allowed classes: introduction rules -/
theorem allowed_intro (X : Ctx) (s : St) (v : ℕ) (hav : bitS s.av v = true)
    (hA : s.fr ≠ 0 ∨ bitS s.mp v = true ∨ bitS s.mq v = true)
    (hF : ¬ (5 < s.c3 ∧ bitS X.m3 v = true)) : bitS (allowed X s) v = true := by
  unfold allowed bitS at *
  simp only [testBit_lor9, testBit_clr9, testBit_land9, ltN_eq9, beq_eq9]
  by_cases hc3 : 5 < s.c3
  · have hm3 : X.m3.testBit (16 * v) = false := by
      by_contra hh
      exact hF ⟨hc3, by simpa using hh⟩
    simp [hc3, hm3, hav]
    rcases hA with h | h | h
    · simp [h, hav]
    · simp [h, hav]
    · simp [h, hav]
  · simp [hc3, hav]
    rcases hA with h | h | h
    · simp [h, hav]
    · simp [h, hav]
    · simp [h, hav]

theorem allowed_intro_mf (X : Ctx) (s : St) (v : ℕ) (hmf : bitS s.mf v = true)
    (hav : bitS s.av v = true) : bitS (allowed X s) v = true := by
  unfold allowed bitS at *
  simp only [testBit_lor9, testBit_clr9, testBit_land9]
  simp [hmf, hav]

end LRSpectrumFull.NineSound
