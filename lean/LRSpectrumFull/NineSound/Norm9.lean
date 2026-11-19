/-
# Nine runners, soundness part 5a: the existence of a normalised good class set from a failing `lemma7Check 8 p`

`exists_good_of_not_check`: for a prime `p > 11`, `lemma7Check 8 p ≠ true` gives a class set `V` with `Good9 p V`.

* the failing tuple `L` of `lemma7Check` is 8 distinct admissible classes mod `9p`, with at most 6 multiples of 3,
  covering the window (`coversAt_iff`, `sideOK_eight`, `admissible_mem9`);
* the unit normalisation (`good9_normalise`): pick `v0 ∈ L`, `u` with `v0 u ≡ 1 (p)`, and `b ≡ 1 (3)`, `b ≡ u (p)` by the Chinese
  remainder theorem; `b` is prime to `9p`, and `x ↦ red (9p) (b x)` preserves admissibility, the number of multiples of 3
  and the covering (the time `j` is covered by the image of `x` iff the time `red (9p) (b j)` is covered by `x`; this time
  lies in the window because `b` is a unit), and sends `v0` to a class with `red p _ = 1`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.Pm9

namespace LRSpectrumFull.NineSound

open LRSpectrumFull LRSpectrumFull.NineProbe Finset

/-- `red p (red M x) = red p x` for every multiple `M` of the odd modulus `p` (generalises `red_red3`) -/
theorem red_red_dvd {p M : ℕ} (hp : 0 < p) (hp2 : p % 2 = 1) (hpM : p ∣ M) (hM : 0 < M) (x : ℕ) :
    red p (red M x) = red p x := by
  have h1 : PM p (red M x) (red p (red M x)) := pm_red p _ hp
  have h2 : PM M x (red M x) := pm_red M x hM
  have h3 : PM p x (red p x) := pm_red p x hp
  have h2' : PM p x (red M x) := pm_mono hpM hM h2
  have h4 := pm_trans hp (pm_symm hp h1) (pm_trans hp (pm_symm hp h2') h3)
  have e1 := red_le p (red M x) hp
  have e2 := red_le p x hp
  exact pm_inj (by omega) (by omega) h4

theorem red_pos {M y : ℕ} (hM : 0 < M) (hy : ¬ M ∣ y) : 1 ≤ red M y := by
  unfold red
  have h := Nat.mod_lt y hM
  have h0 : y % M ≠ 0 := fun h' => hy (Nat.dvd_of_mod_eq_zero h')
  omega

/-- the normalisation map of the class set: multiply by `b` and fold mod `9p` -/
def nrm (p b x : ℕ) : ℕ := red (9 * p) (b * x)

theorem good9_normalise {p : ℕ} (hp : p.Prime) (h3 : 3 < p) (hp2 : p % 2 = 1)
    (V0 : Finset ℕ) (hadm : V0 ⊆ AdmC (9 * p) p) (hcard : V0.card ≤ 8)
    (hcov : ∀ j ∈ Win (9 * p), ∃ x ∈ V0, covM (9 * p) j x)
    (hside : (V0.filter (fun x => 3 ∣ x)).card ≤ 6) (hne : V0.Nonempty) :
    ∃ V, Good9 p V := by
  obtain ⟨v0, hv0⟩ := hne
  have hp0 : 0 < p := hp.pos
  have hM : 0 < 9 * p := by omega
  have hnd0 : ¬ p ∣ v0 := not_dvd_of_adm (hadm hv0)
  have hcop : Nat.Coprime v0 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd0).symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega : 1 < p)
  have hco3p : Nat.Coprime 3 p := by
    rw [Nat.coprime_primes Nat.prime_three hp]; omega
  obtain ⟨b, hb3, hbp⟩ := Nat.chineseRemainder hco3p 1 u
  have hb3' : b % 3 = 1 := by
    have := hb3
    unfold Nat.ModEq at this
    omega
  have hbv : b * v0 % p = 1 := by
    have h1 : b * v0 ≡ u * v0 [MOD p] := Nat.ModEq.mul_right v0 hbp
    have h2 : u * v0 % p = 1 := by rw [mul_comm]; exact hu
    unfold Nat.ModEq at h1
    rw [h1, h2]
  have hnb : ¬ p ∣ b := fun h => by
    have h0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right h v0)
    rw [hbv] at h0
    exact absurd h0 one_ne_zero
  have hnb3 : ¬ 3 ∣ b := by omega
  have hc9 : Nat.Coprime 9 b := by
    have h := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnb3)
    simpa using h
  have hcp : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnb
  have hcopM : Nat.Coprime (9 * p) b := Nat.Coprime.mul hc9 hcp
  have hnbx : ∀ x ∈ V0, ¬ p ∣ b * x := fun x hx h =>
    ((hp.dvd_mul).mp h).elim hnb (not_dvd_of_adm (hadm hx))
  refine ⟨V0.image (nrm p b), ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact adm_of_red p (9 * p) (b * x) hM (dvd_mul_left p 9) (hnbx x hx) hp0
  · exact card_image_le.trans hcard
  · intro j hj
    have hj' := hj
    simp only [Win, mem_Icc] at hj'
    have hndiv : ¬ (9 * p) ∣ b * j := by
      intro h
      have h' : (9 * p) ∣ j * b := by rw [mul_comm j b]; exact h
      have h2 := hcopM.dvd_of_dvd_mul_right h'
      have := Nat.le_of_dvd (by omega) h2
      omega
    have hj'1 : 1 ≤ red (9 * p) (b * j) := red_pos hM hndiv
    have hj'2 : 2 * red (9 * p) (b * j) ≤ 9 * p := red_le _ _ hM
    have hj'W : red (9 * p) (b * j) ∈ Win (9 * p) := by
      simp only [Win, mem_Icc]; omega
    obtain ⟨x, hx, hcx⟩ := hcov _ hj'W
    refine ⟨nrm p b x, mem_image_of_mem _ hx, ?_⟩
    unfold nrm
    rw [covM_red _ _ _ hM]
    have h1 : covM (9 * p) x (red (9 * p) (b * j)) := by
      unfold covM at hcx ⊢
      rwa [mul_comm (red (9 * p) (b * j)) x] at hcx
    have h2 := (covM_red (9 * p) x (b * j) hM).1 h1
    unfold covM at h2 ⊢
    have e : j * (b * x) = x * (b * j) := by ring
    rw [e]
    exact h2
  · have hsub : (V0.image (nrm p b)).filter (fun x => 3 ∣ x) ⊆
        (V0.filter (fun x => 3 ∣ x)).image (nrm p b) := by
      intro y hy
      obtain ⟨hyV, hy3⟩ := mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hyV
      have h3b : 3 ∣ b * x :=
        (red_dvd 3 (9 * p) (b * x) hM ⟨3 * p, by ring⟩).1 hy3
      have h3x : 3 ∣ x := ((Nat.Prime.dvd_mul Nat.prime_three).1 h3b).resolve_left hnb3
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, h3x⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans hside)
  · refine ⟨nrm p b v0, mem_image_of_mem _ hv0, ?_⟩
    unfold nrm
    rw [red_red_dvd hp0 hp2 (dvd_mul_left p 9) hM]
    unfold red
    rw [hbv]
    omega

theorem exists_good_of_not_check {p : ℕ} (hp : p.Prime) (h11 : 11 < p) (h : lemma7Check 8 p ≠ true) :
    ∃ V, Good9 p V := by
  classical
  unfold lemma7Check at h
  rw [ne_eq, List.all_eq_true] at h
  push Not at h
  obtain ⟨L, hL, hbad⟩ := h
  have hb : sideOK 8 L = true ∧ coversWindow 8 p L = true := by
    revert hbad
    cases h1 : sideOK 8 L <;> cases h2 : coversWindow 8 p L <;> simp
  obtain ⟨hs, hc⟩ := hb
  unfold tuples at hL
  rw [List.mem_sublistsLen] at hL
  obtain ⟨hsub, hlen⟩ := hL
  have hLnd : (admissible 8 p).Nodup := List.nodup_range.filter _
  have hnd : L.Nodup := hsub.nodup hLnd
  have hp3 : 3 < p := by omega
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hcardL : L.toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hnd]; exact hlen
  have hadm : L.toFinset ⊆ AdmC (9 * p) p := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have h := (admissible_mem9 p x).1 (hsub.subset hx)
    simp only [AdmC, Win, mem_filter, mem_Icc]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  have hne : L.toFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hcov : ∀ j ∈ Win (9 * p), ∃ x ∈ L.toFinset, covM (9 * p) j x := by
    intro j hj
    simp only [Win, mem_Icc] at hj
    unfold coversWindow at hc
    rw [List.all_eq_true] at hc
    have hjm : j ∈ (List.range (((8 + 1) * p) / 2 + 1)).filter (fun j => 1 ≤ j) := by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      omega
    have h' := hc j hjm
    rw [List.any_eq_true] at h'
    obtain ⟨v, hv, hcv⟩ := h'
    exact ⟨v, List.mem_toFinset.mpr hv, (coversAt_iff p j v).1 hcv⟩
  have hside : (L.toFinset.filter (fun x => 3 ∣ x)).card ≤ 6 := by
    rw [sideOK_eight, decide_eq_true_eq] at hs
    have hnd3 : (L.filter (fun v => v % 3 == 0)).Nodup := hnd.filter _
    have hE : L.toFinset.filter (fun x => 3 ∣ x) = (L.filter (fun v => v % 3 == 0)).toFinset := by
      ext x
      simp [Nat.dvd_iff_mod_eq_zero]
    rw [hE, List.toFinset_card_of_nodup hnd3]
    exact hs
  exact good9_normalise hp hp3 hp2 L.toFinset hadm (by omega) hcov hside hne

/-- **The existence of `V`**: with no normalised good class set, the Lemma 7 check at `k = 8` passes. -/
theorem lemma7Check_of_noGood {p : ℕ} (hp : p.Prime) (h11 : 11 < p) (hno : ¬ ∃ V, Good9 p V) :
    lemma7Check 8 p = true := by
  by_contra h
  exact hno (exists_good_of_not_check hp h11 h)

end LRSpectrumFull.NineSound
