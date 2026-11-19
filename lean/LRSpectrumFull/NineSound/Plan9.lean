/-
# Nine runners, part 7b: the plan layer (E0, E3, E5 and the assembly) ported from `EightPlan` / `EightE5`

Port of `EightPlan` (E0, E3, NUM, AM-GM) and `EightE5` (adjacent pair, planar rounding, assembly) from
`k = 7` speeds (eight runners) to `k = 8` speeds (nine runners):

    E8 (Fin 7)                       E9 (Fin 8)
    8, 3, 5, 7  (j <= 8, 840)        8, 9, 5, 7  (j <= 9, 2520 = lcm 1..9)
    28 = C(8,2), 28^6, 28^42, 7^7    36 = C(9,2), 36^7, 36^56, 8^8
    LRC6, 1/7, rounding 1/56         LRC7, 1/8, rounding 1/72, 1/8 - 1/72 = 1/9
    27 primes 31..163                S36 = 36 primes 53..241 (without 59, 73)

What is PROVED here (no hypothesis): `numeric9` (the arithmetic `36^56 < 8^8 * 2520 * prod S36`, kernel),
`e3_lcm_dvd9`, `amgm8`, `e5_amgm9`, `exists_adjacent_pair9`, `mssGap8_holds`, `e5_prod9` (the rounding step:
with `LRC7`, a primitive `v` with `8^8 prod v > 36^56` has `1/9 <= ML v`), `e0_primitive9`.

What is TAKEN AS HYPOTHESIS in the final theorem `nine_runners_of`, loudly:
* `h7 : LRC7` (LRC for seven speeds, eight runners; the statement of `EightRunnersReal.eight_runners_unconditional_real`);
* `hS : forall p in S36, forall w, IsCE9 w -> exists i, p | w i`, the per-prime divisibility facts.  Each instance
  is the conclusion of `e2_prime_dvd9_of_tables` (Check9G) for a prime whose generated tables and certificates are
  accepted; the campaign discharges them prime by prime (see `Plan9Glue`, `PrimeData`).

No `native_decide`, no `sorry`, no axiom.  `Stair9.e5b_staircase` is the clean extraction of the staircase lemma.
-/

import LRSpectrumFull.NineSound.Fold
import LRSpectrumFull.NineSound.Stair9
import LRSpectrumFull.Delta2Boundary
import LRSpectrumFull.NearestIntLipschitz

namespace LRSpectrumFull.NineSound.Plan9

open LRSpectrumFull LRSpectrumFull.NineSound

/-! ## The prime set -/

/-- the 36 campaign primes: the primes 53 to 241 except 59 and 73 -/
def S36L : List ℕ :=
  [53, 61, 67, 71, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241]

def S36 : Finset ℕ := S36L.toFinset

theorem S36L_nodup : S36L.Nodup := by decide +kernel

theorem mem_S36 {p : ℕ} : p ∈ S36 ↔ p ∈ S36L := List.mem_toFinset

theorem S36_card : S36.card = 36 := by
  rw [S36, List.toFinset_card_of_nodup S36L_nodup]; rfl

theorem S36_prod : ∏ p ∈ S36, p = S36L.prod := by
  rw [S36, List.prod_toFinset _ S36L_nodup]; simp

theorem S36_pairwise : ∀ a ∈ S36L, ∀ b ∈ S36L, a ≠ b → Nat.Coprime a b := by decide +kernel

theorem S36_cop2520 : ∀ p ∈ S36L, Nat.Coprime 2520 p := by decide +kernel

/-- **NUM (kernel).** `36^56 < 8^8 * (2520 * prod S36)`. -/
theorem numeric9 : (36 : ℕ) ^ 56 < 8 ^ 8 * (2520 * ∏ p ∈ S36, p) := by
  rw [S36_prod]; decide +kernel

/-! ## E0: gcd reduction (local copies, generic in `k`) -/

theorem gap_smul9 {k : ℕ} (c : ℤ) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => c * v i) t = gap v ((c : ℝ) * t) := by
  unfold gap
  congr 1; funext i; congr 1; push_cast; ring

theorem ML_smul9 {k : ℕ} (c : ℤ) (hc : c ≠ 0) (v : Fin (k + 1) → ℤ) :
    ML (fun i => c * v i) = ML v := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hrange : Set.range (gap (fun i => c * v i)) = Set.range (gap v) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨(c : ℝ) * t, (gap_smul9 c v t).symm⟩
    · rintro ⟨s, rfl⟩
      refine ⟨s / (c : ℝ), ?_⟩
      rw [gap_smul9]; congr 1; field_simp
  unfold ML; rw [hrange]

theorem e0_primitive9
    (h : ∀ v : Fin 8 → ℤ, (∀ i, 0 < v i) → Finset.univ.gcd v = 1 → 1 / 9 ≤ ML v)
    (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 9 ≤ ML v := by
  obtain ⟨w, hw, hg1⟩ := Finset.extract_gcd v (Finset.univ_nonempty (α := Fin 8))
  have hg0 : 0 ≤ Finset.univ.gcd v :=
    Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := v))
  generalize Finset.univ.gcd v = g at hw hg0
  have hw' : ∀ i, v i = g * w i := fun i => hw i (Finset.mem_univ i)
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h' | h'
    · exact h'
    · exfalso; have := hv 0; rw [hw' 0, ← h'] at this; simp at this
  have hwpos : ∀ i, 0 < w i := fun i => by
    have := hv i
    rw [hw' i] at this
    by_contra hn
    push Not at hn
    nlinarith
  rw [show v = fun i => g * w i from funext hw', ML_smul9 g hgpos.ne' w]
  exact h w hwpos hg1

/-! ## E3: small divisors and the divisibility assembly -/

/-- **E3a (Lemma 4 at the time `1/j`).** For `2 <= j <= 9`, some speed of a counterexample is divisible by `j`. -/
theorem e3_small_divisor9 (v : Fin 8 → ℤ) (hML : ML v < 1 / 9) (j : ℕ) (hj2 : 2 ≤ j)
    (hj9 : j ≤ 9) : ∃ i, (j : ℤ) ∣ v i := by
  by_contra hno
  push Not at hno
  have hjpos : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
  have hgap : (1 : ℝ) / (j : ℝ) ≤ gap v (1 / (j : ℝ)) := by
    apply le_gap
    intro i
    rw [show (v i : ℝ) * (1 / (j : ℝ)) = (v i : ℝ) / (j : ℝ) by ring]
    by_contra hlt
    push Not at hlt
    rw [nearestIntDist_div_lt_iff (v i) j hjpos, one_div_mul_cancel hjR.ne'] at hlt
    have hr0 : v i % (j : ℤ) ≠ 0 := fun h => hno i (Int.dvd_of_emod_eq_zero h)
    have hr1 : 0 ≤ v i % (j : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hjpos.ne')
    have hr2 : v i % (j : ℤ) < j := Int.emod_lt_of_pos _ (by exact_mod_cast hjpos)
    have ha : (1 : ℤ) ≤ v i % j := by omega
    have hb : (1 : ℤ) + v i % j ≤ j := by omega
    have haR : (1 : ℝ) ≤ ((v i % (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast ha
    have hbR : (1 : ℝ) + ((v i % (j : ℤ) : ℤ) : ℝ) ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hb
    simp only [Int.cast_natCast] at hbR
    rcases min_lt_iff.mp hlt with h | h <;> linarith
  have h9 : (1 : ℝ) / 9 ≤ 1 / (j : ℝ) := one_div_le_one_div_of_le hjR (by exact_mod_cast hj9)
  linarith [gap_le_ML v (1 / (j : ℝ))]

/-- **E3 (VERIFIED here).** Pairwise coprime `8, 9, 5, 7` and the primes of `S36` each divide some speed, hence
`2520 * prod S36` divides the product of the speeds. -/
theorem e3_lcm_dvd9 (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) (hML : ML v < 1 / 9)
    (hS : ∀ p ∈ S36, ∃ i, (p : ℤ) ∣ v i) :
    (((2520 * ∏ p ∈ S36, p : ℕ)) : ℤ) ∣ ∏ i, v i := by
  have hdv : ∀ d : ℕ, (∃ i, (d : ℤ) ∣ v i) → (d : ℤ) ∣ ∏ i, v i := by
    rintro d ⟨i, hi⟩
    exact hi.trans (Finset.dvd_prod_of_mem v (Finset.mem_univ i))
  have h8 := hdv 8 (e3_small_divisor9 v hML 8 (by norm_num) (by norm_num))
  have h9 := hdv 9 (e3_small_divisor9 v hML 9 (by norm_num) le_rfl)
  have h5 := hdv 5 (e3_small_divisor9 v hML 5 (by norm_num) (by norm_num))
  have h7 := hdv 7 (e3_small_divisor9 v hML 7 (by norm_num) (by norm_num))
  push_cast at h8 h9 h5 h7
  have c1 : IsCoprime (5 : ℤ) 7 := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have c2 : IsCoprime (9 : ℤ) (5 * 7) := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have c3 : IsCoprime (8 : ℤ) (9 * (5 * 7)) := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have h2520 : (2520 : ℤ) ∣ ∏ i, v i := by
    have := c3.mul_dvd h8 (c2.mul_dvd h9 (c1.mul_dvd h5 h7))
    norm_num at this
    exact this
  have hSd : (∏ p ∈ S36, ((p : ℕ) : ℤ)) ∣ ∏ i, v i := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      simp only [Function.onFun]
      rw [Nat.isCoprime_iff_coprime]
      exact S36_pairwise a (mem_S36.mp (Finset.mem_coe.mp ha)) b (mem_S36.mp (Finset.mem_coe.mp hb)) hab
    · intro p hp
      exact hdv p (hS p hp)
  have hcop : IsCoprime (2520 : ℤ) (∏ p ∈ S36, ((p : ℕ) : ℤ)) := by
    apply IsCoprime.prod_right
    intro p hp
    rw [show (2520 : ℤ) = ((2520 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    exact S36_cop2520 p (mem_S36.mp hp)
  have := hcop.mul_dvd h2520 hSd
  push_cast
  exact this

/-! ## E5: AM-GM and the planar rounding step -/

/-- AM-GM in integer form at eight variables: `8^8 prod v <= (sum v)^8`. -/
theorem amgm8 (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 8 ^ 8 * ∏ i, v i ≤ (∑ i, v i) ^ 8 := by
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 8)), (0 : ℝ) ≤ (v i : ℝ) :=
    fun i _ => by exact_mod_cast (hv i).le
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin 8))
    (fun _ => (1 / 8 : ℝ)) (fun i => (v i : ℝ)) (fun _ _ => by norm_num) (by simp) hz
  set g := ∏ i, (v i : ℝ) ^ (1 / 8 : ℝ) with hg
  have hg0 : 0 ≤ g := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hz i (Finset.mem_univ i)) _)
  have hg8 : g ^ 8 = ∏ i, (v i : ℝ) := by
    rw [hg, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i hi)]
    norm_num
  have hsum : (∑ i, (1 / 8 : ℝ) * (v i : ℝ)) = (∑ i, (v i : ℝ)) / 8 := by
    rw [← Finset.mul_sum]; ring
  rw [hsum] at hgm
  have hpow : g ^ 8 ≤ ((∑ i, (v i : ℝ)) / 8) ^ 8 := pow_le_pow_left₀ hg0 hgm 8
  rw [hg8, div_pow] at hpow
  have hR : (8 : ℝ) ^ 8 * ∏ i, (v i : ℝ) ≤ (∑ i, (v i : ℝ)) ^ 8 := by
    rw [le_div_iff₀ (by norm_num)] at hpow
    linarith
  exact_mod_cast hR

/-- `8^8 prod v > 36^56` gives `sum v > 36^7`. -/
theorem e5_amgm9 (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i)
    (hprod : (36 : ℤ) ^ 56 < 8 ^ 8 * ∏ i, v i) : (36 : ℤ) ^ 7 < ∑ i, v i := by
  by_contra hle
  push Not at hle
  have hs0 : 0 ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ => (hv i).le)
  have h1 := amgm8 v hv
  have h2 : (∑ i, v i) ^ 8 ≤ ((36 : ℤ) ^ 7) ^ 8 := pow_le_pow_left₀ hs0 hle 8
  have h3 : ((36 : ℤ) ^ 7) ^ 8 = 36 ^ 56 := by norm_num
  omega

/-- Adjacent slope pair: `z_i/v_i < z_j/v_j` and no `k` has the mediant slope. -/
theorem exists_adjacent_pair9 (v z : Fin 8 → ℤ) (hv : ∀ i, 0 < v i)
    (hnp : ∃ a b, z a * v b ≠ z b * v a) :
    ∃ i j, z i * v j < z j * v i ∧ ∀ k, (z i + z j) * v k ≠ (v i + v j) * z k := by
  classical
  set P : Finset (Fin 8 × Fin 8) :=
    Finset.univ.filter (fun p => z p.1 * v p.2 < z p.2 * v p.1) with hP
  have hPne : P.Nonempty := by
    obtain ⟨a, b, hab⟩ := hnp
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨(a, b), by simp [hP, h]⟩
    · exact ⟨(b, a), by simp [hP]; linarith⟩
  set r : Fin 8 → ℚ := fun k => (z k : ℚ) / v k with hr
  obtain ⟨⟨i, j⟩, hmem, hmin⟩ := P.exists_min_image (fun p => r p.2 - r p.1) hPne
  have hij : z i * v j < z j * v i := by simpa [hP] using hmem
  refine ⟨i, j, hij, fun k hk => ?_⟩
  have hvi : (0 : ℚ) < v i := by exact_mod_cast hv i
  have hvj : (0 : ℚ) < v j := by exact_mod_cast hv j
  have hvk : (0 : ℚ) < v k := by exact_mod_cast hv k
  have hijq : (z i : ℚ) * v j < z j * v i := by exact_mod_cast hij
  have hkq : ((z i : ℚ) + z j) * v k = (v i + v j) * z k := by exact_mod_cast hk
  have h1 : z i * v k < z k * v i := by
    have : (z i : ℚ) * v k < z k * v i := by nlinarith
    exact_mod_cast this
  have hmemk : (i, k) ∈ P := by simp [hP, h1]
  have hle := hmin (i, k) hmemk
  simp only [hr] at hle
  have hkj : (z k : ℚ) * v j < z j * v k := by nlinarith
  have : (z k : ℚ) / v k < z j / v j := by
    rw [div_lt_div_iff₀ hvk hvj]; exact hkj
  linarith

/-- **The rounding step at `n = 8`, `l = 36`.** From `LRC7` and a vector `z`, not parallel to `v`, with
`|36 z_i - sigma v_i| <= 1`, a witness time of loneliness `1/9 = 1/8 - 1/72`. -/
theorem mssGap8_holds (h7 : LRC7) (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i)
    (hz : ∃ z : Fin 8 → ℤ, ∃ σ : ℚ, (∃ a b, z a * v b ≠ z b * v a) ∧
      ∀ i, |(36 : ℚ) * z i - σ * v i| ≤ 1) : 1 / 9 ≤ ML v := by
  obtain ⟨z, σ, hnp, hzb⟩ := hz
  obtain ⟨i, j, hij, hmed⟩ := exists_adjacent_pair9 v z hv hnp
  have hij' : i ≠ j := by
    rintro rfl; exact lt_irrefl _ hij
  set c : Fin 8 → ℤ := fun k => (z i + z j) * v k - (v i + v j) * z k with hc
  have hc0 : ∀ k, c k ≠ 0 := fun k h => hmed k (by simp only [hc] at h; linarith)
  have hcj : c j = - c i := by simp only [hc]; ring
  set u : Fin (6 + 1) → ℤ := fun m => |c (j.succAbove m)| with hu
  have hupos : ∀ m, 0 < u m := fun m => abs_pos.mpr (hc0 _)
  obtain ⟨τ, hτ⟩ := (le_ML_iff_exists_far u _).mp (h7 u hupos)
  have habs : ∀ k, nearestIntDist ((|c k| : ℤ) * τ : ℝ) = nearestIntDist ((c k : ℝ) * τ) := by
    intro k
    rcases abs_choice (c k) with h | h <;> rw [h]
    push_cast; rw [neg_mul, nearestIntDist_neg]
  have hsucc : ∀ k, k ≠ j → 1 / ((6 : ℝ) + 2) ≤ nearestIntDist ((c k : ℝ) * τ) := by
    intro k hk
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hk
    have := hτ m
    simp only [hu] at this
    rwa [habs] at this
  have hall : ∀ k, 1 / ((6 : ℝ) + 2) ≤ nearestIntDist ((c k : ℝ) * τ) := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [hcj]; push_cast; rw [neg_mul, nearestIntDist_neg]
      exact hsucc i hij'
    · exact hsucc k hk
  -- rounding
  set a1 : ℝ := -((v i : ℝ) + v j) * τ with ha1
  set k1 : ℤ := round a1 with hk1
  set r : ℝ := a1 - k1 with hr
  have hr2 : |r| ≤ 1 / 2 := abs_sub_round a1
  set s : ℝ := (σ : ℝ) / 36 with hs
  set t : ℝ := ((z i : ℝ) + z j) * τ + r * s with ht
  refine (le_ML_iff_exists_far v (1 / 9)).mpr ⟨t, fun k => ?_⟩
  have hd : |(z k : ℝ) - s * v k| ≤ 1 / 36 := by
    have h := hzb k
    have h' : |(36 : ℝ) * z k - (σ : ℝ) * v k| ≤ 1 := by exact_mod_cast h
    have : (z k : ℝ) - s * v k = ((36 : ℝ) * z k - (σ : ℝ) * v k) / 36 := by
      rw [hs]; ring
    rw [this, abs_div]; norm_num; linarith
  have hid : (v k : ℝ) * t = ((c k : ℝ) * τ - r * ((z k : ℝ) - s * v k)) + ((-(k1 * z k) : ℤ) : ℝ) := by
    simp only [ht, hc, hr, ha1]; push_cast; ring
  rw [hid, nearestIntDist_add_int]
  have hL := nearestIntDist_lipschitz ((c k : ℝ) * τ - r * ((z k : ℝ) - s * v k)) ((c k : ℝ) * τ)
  have hsmall : |r * ((z k : ℝ) - s * v k)| ≤ 1 / 72 := by
    rw [abs_mul]
    calc |r| * |(z k : ℝ) - s * v k| ≤ (1 / 2) * (1 / 36) :=
          mul_le_mul hr2 hd (abs_nonneg _) (by norm_num)
      _ = 1 / 72 := by norm_num
  have hk := hall k
  have heq : (c k : ℝ) * τ - r * ((z k : ℝ) - s * v k) - (c k : ℝ) * τ
      = -(r * ((z k : ℝ) - s * v k)) := by ring
  rw [heq, abs_neg] at hL
  have := (abs_le.mp hL).1
  norm_num at hk ⊢
  linarith

/-- **E5 (product form), nine runners.** `LRC7`, `gcd v = 1` and `8^8 prod v > 36^56` give `1/9 <= ML v`. -/
theorem e5_prod9 (h7 : LRC7) (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i)
    (hg : Finset.univ.gcd v = 1) (hprod : (36 : ℤ) ^ 56 < 8 ^ 8 * ∏ i, v i) : 1 / 9 ≤ ML v := by
  have hsum := e5_amgm9 v hv hprod
  exact mssGap8_holds h7 v hv
    (Stair9.e5b_staircase hv hg 36 (by norm_num) (by simpa using hsum))

/-! ## The assembly -/

/-- **LRC for nine runners, from `LRC7` and the 36 per-prime divisibility facts.**  The hypothesis `hS` is the
open part: for each `p` in `S36` and each primitive counterexample `w`, some speed is divisible by `p`. -/
theorem nine_runners_of (h7 : LRC7)
    (hS : ∀ p ∈ S36, ∀ w : Fin 8 → ℤ, IsCE9 w → ∃ i, (p : ℤ) ∣ w i)
    (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 9 ≤ ML v := by
  refine e0_primitive9 (fun w hw hg => ?_) v hv
  by_contra hlt
  push Not at hlt
  have hce : IsCE9 w := ⟨hw, hg, hlt⟩
  have hdvd := e3_lcm_dvd9 w hw hlt (fun p hp => hS p hp w hce)
  have hpos : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hle := Int.le_of_dvd hpos hdvd
  have hnum : ((36 : ℕ) ^ 56 : ℤ) < ((8 ^ 8 * (2520 * ∏ p ∈ S36, p) : ℕ) : ℤ) := by
    exact_mod_cast numeric9
  have hprod : (36 : ℤ) ^ 56 < 8 ^ 8 * ∏ i, w i := by
    push_cast at hnum hle
    nlinarith
  exact absurd (e5_prod9 h7 w hw hg hprod) (not_le.mpr hlt)

end LRSpectrumFull.NineSound.Plan9
