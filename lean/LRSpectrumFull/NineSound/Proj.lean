/-
# Nine runners, soundness part 1b: projection of a cover to the coarse moduli 3p and p

The hierarchical certificate for `lemma7Check 8 p` has three trees, at the moduli `p`, `3p`, `9p`
(`NineProbe.Ctx.lvl = 0, 1, 2`).  A class set `D` covering the window of the fine modulus `9p`
covers the windows of the coarse moduli `3p` and `p` once the classes are read there:

* `covM M j x`           the covering relation at modulus `M` with threshold `1/9`
                         (`coversAt 8 p j x` is `covM (9p) j x`, `coversAt_iff`);
* `covM_scale`           a coarse time `j` embeds as `c j` at modulus `c M`, and the covering of the
                         embedded time at the fine modulus is the covering at the coarse modulus;
* `win_scale`, `proj_cover`   the window of `M'` embeds in the window of `c M'` (`M'` odd);
* `red M x`              the folded class `min (x mod M) (M - x mod M)`; `covM_red` the covering
                         relation depends on the class only through `red`; `red_dvd` divisibility
                         by a divisor `g` of `M` (3 and `p` for `M = 3p`, `p`) is preserved,
                         `red_mem` it lands in the admissible range;
* `proj_cover_red`, `proj_cover_3p_p`   the two projection statements used by the checker semantics.

No `native_decide`, no `sorry`, no axiom.
-/

import Mathlib
import LRSpectrumFull.LRCFourRunnersCore

namespace LRSpectrumFull.NineSound

open LRSpectrumFull

/-- distance of `y` to the nearest multiple of `M` (natural-number form) -/
def nd (M y : ℕ) : ℕ := min (y % M) (M - y % M)

/-- `x` covers the time `j / M`: the distance of `j x / M` to the integers is below `1/9` -/
def covM (M j x : ℕ) : Prop := 9 * nd M (j * x) < M

instance (M j x : ℕ) : Decidable (covM M j x) := by unfold covM; infer_instance

/-- `coversAt 8 p` is the covering relation at modulus `9p` -/
theorem coversAt_iff (p j v : ℕ) : coversAt 8 p j v = true ↔ covM (9 * p) j v := by
  simp [coversAt, covM, nd]

/-- the window of times at modulus `M` -/
def Win (M : ℕ) : Finset ℕ := Finset.Icc 1 (M / 2)

theorem nd_scale (c M y : ℕ) : nd (c * M) (c * y) = c * nd M y := by
  unfold nd
  rw [Nat.mul_mod_mul_left]
  have h : c * M - c * (y % M) = c * (M - y % M) := (Nat.mul_sub c M (y % M)).symm
  rw [h]
  rcases le_total (y % M) (M - y % M) with h1 | h1
  · rw [min_eq_left h1, min_eq_left (Nat.mul_le_mul_left c h1)]
  · rw [min_eq_right h1, min_eq_right (Nat.mul_le_mul_left c h1)]

/-- **Scaling.**  The time `c j` at modulus `c M` is covered by `x` iff `j` is covered at modulus `M`. -/
theorem covM_scale (c M j x : ℕ) (hc : 0 < c) : covM (c * M) (c * j) x ↔ covM M j x := by
  unfold covM
  rw [show c * j * x = c * (j * x) by ring, nd_scale c M (j * x),
    show 9 * (c * nd M (j * x)) = c * (9 * nd M (j * x)) by ring]
  exact Nat.mul_lt_mul_left hc

/-- the window of an odd modulus `M'` embeds in the window of `c M'` through `j ↦ c j` -/
theorem win_scale (c M' j : ℕ) (hc : 0 < c) (hodd : M' % 2 = 1) (hj : j ∈ Win M') :
    c * j ∈ Win (c * M') := by
  unfold Win at *
  rw [Finset.mem_Icc] at *
  obtain ⟨h1, h2⟩ := hj
  have h3 : 2 * j + 1 ≤ M' := by omega
  have h4 : c * (2 * j + 1) ≤ c * M' := Nat.mul_le_mul_left c h3
  have h5 : c * (2 * j + 1) = 2 * (c * j) + c := by ring
  refine ⟨?_, ?_⟩
  · have : 1 ≤ c * j := Nat.mul_pos hc h1
    omega
  · omega

/-- **Projection.**  If `D` covers the window of the fine modulus `c M'`, it covers the window of
the coarse modulus `M'`. -/
theorem proj_cover (c M' : ℕ) (hc : 0 < c) (hodd : M' % 2 = 1) (D : Finset ℕ)
    (hD : ∀ j ∈ Win (c * M'), ∃ x ∈ D, covM (c * M') j x) :
    ∀ j ∈ Win M', ∃ x ∈ D, covM M' j x := by
  intro j hj
  obtain ⟨x, hx, hcov⟩ := hD (c * j) (win_scale c M' j hc hodd hj)
  exact ⟨x, hx, (covM_scale c M' j x hc).1 hcov⟩

/-! ## Folding the classes at the coarse modulus -/

theorem nd_congr (M y z : ℕ) (hM : 0 < M) (h : y % M = z % M ∨ (y + z) % M = 0) :
    nd M y = nd M z := by
  unfold nd
  rcases h with h | h
  · rw [h]
  · have hy := Nat.mod_lt y hM
    have hz := Nat.mod_lt z hM
    have hs : (y % M + z % M) % M = 0 := by rw [← Nat.add_mod]; exact h
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hs
    generalize y % M = r at *
    generalize z % M = s at *
    rcases k with _ | _ | k
    · have h1 : r = 0 := by omega
      have h2 : s = 0 := by omega
      rw [h1, h2]
    · have e1 : M - r = s := by omega
      have e2 : M - s = r := by omega
      rw [e1, e2, min_comm]
    · exfalso
      have : M * (k + 1 + 1) = M * k + 2 * M := by ring
      omega

/-- the folded class of `x` at modulus `M` -/
def red (M x : ℕ) : ℕ := min (x % M) (M - x % M)

/-- **Folding.**  The covering relation depends on the class only through its fold. -/
theorem covM_red (M j x : ℕ) (hM : 0 < M) : covM M j (red M x) ↔ covM M j x := by
  have key : nd M (j * red M x) = nd M (j * x) := by
    unfold red
    have hx := Nat.div_add_mod x M
    have ha := Nat.mod_lt x hM
    generalize x / M = d at hx
    generalize x % M = a at hx ha ⊢
    subst hx
    by_cases hle : a ≤ M - a
    · rw [min_eq_left hle]
      apply nd_congr M _ _ hM
      left
      have : j * (M * d + a) = M * (j * d) + j * a := by ring
      rw [this, Nat.mul_add_mod]
    · rw [min_eq_right (by omega)]
      apply nd_congr M _ _ hM
      right
      obtain ⟨b, hb⟩ : ∃ b, M = a + b := ⟨M - a, by omega⟩
      have hMa : M - a = b := by omega
      rw [hMa]
      have : j * b + j * (M * d + a) = M * (j + j * d) := by rw [hb]; ring
      rw [this]
      exact Nat.mul_mod_right M _
  unfold covM
  rw [key]

/-- divisibility by a divisor of the modulus survives the fold -/
theorem red_dvd (g M x : ℕ) (hM : 0 < M) (hg : g ∣ M) : g ∣ red M x ↔ g ∣ x := by
  have hx := Nat.div_add_mod x M
  have ha := Nat.mod_lt x hM
  have hxg : g ∣ x ↔ g ∣ x % M := by
    conv_lhs => rw [← hx]
    exact Nat.dvd_add_right (Dvd.dvd.mul_right hg _)
  rw [hxg]
  unfold red
  by_cases hle : x % M ≤ M - x % M
  · rw [min_eq_left hle]
  · rw [min_eq_right (by omega)]
    constructor
    · intro h
      have := Nat.dvd_sub hg h
      rwa [Nat.sub_sub_self ha.le] at this
    · intro h
      exact Nat.dvd_sub hg h

/-- the fold of a class prime to `g`-multiples lands in the admissible range `[1, M/2]` -/
theorem red_mem (p M x : ℕ) (hM : 0 < M) (hpM : p ∣ M) (hx : ¬ p ∣ x) :
    1 ≤ red M x ∧ red M x ≤ M / 2 ∧ ¬ p ∣ red M x := by
  have h3 : ¬ p ∣ red M x := fun h => hx ((red_dvd p M x hM hpM).1 h)
  have ha := Nat.mod_lt x hM
  refine ⟨?_, ?_, h3⟩
  · by_contra hlt
    have h0 : red M x = 0 := by omega
    exact h3 (by rw [h0]; exact dvd_zero p)
  · unfold red
    omega

/-- **Projection with folding.**  A class set `D` of classes prime to `p` covering the window of
`c M'` (with `p ∣ M'`) gives a set `E` of folded admissible classes at modulus `M'` (at most `|D|`
of them) covering the window of `M'`. -/
theorem proj_cover_red (c M' p : ℕ) (hc : 0 < c) (hM' : 0 < M') (hodd : M' % 2 = 1)
    (hpM : p ∣ M') (D : Finset ℕ) (hDp : ∀ x ∈ D, ¬ p ∣ x)
    (hD : ∀ j ∈ Win (c * M'), ∃ x ∈ D, covM (c * M') j x) :
    ∃ E : Finset ℕ, E.card ≤ D.card ∧ (∀ y ∈ E, 1 ≤ y ∧ y ≤ M' / 2 ∧ ¬ p ∣ y) ∧
      ∀ j ∈ Win M', ∃ y ∈ E, covM M' j y := by
  classical
  refine ⟨D.image (red M'), Finset.card_image_le, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact red_mem p M' x hM' hpM (hDp x hx)
  · intro j hj
    obtain ⟨x, hx, hcov⟩ := proj_cover c M' hc hodd D hD j hj
    exact ⟨red M' x, Finset.mem_image_of_mem _ hx, (covM_red M' j x hM').2 hcov⟩

end LRSpectrumFull.NineSound
