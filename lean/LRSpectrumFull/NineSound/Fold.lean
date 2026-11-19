/-
# Nine runners, soundness part 1a: the odd-modulus fold, padding and the divisor-complete step

The nine-runner chain (Rosenfeld's chain at `k = 8` speeds, modulus `q = 9p`) is `EightPlan` with
`7 -> 8`, `8p -> 9p`, and the single side prime `2 -> 3`.  This file proves, in the style of
`EightPlan`, the part of that chain which is purely about the odd modulus and the side prime 3:

* `fold_facts9`      folding a speed mod `9p` into `[1, 9p/2]`; divisibility by 3 is preserved
                     (this is the point where `8p` (even) and `9p` (odd) differ);
* `padding9`         eight padding classes, none divisible by 3 or by `p`, valid for `p > 11`;
* `nid_ge_of_uncovered9`   an uncovered time has distance `>= 1/9`;
* `admissible_mem9`, `sideOK_eight`   the `lemma7Check 8 p` primitives, unfolded;
* `e4_three9`        the divisor-complete step: at most 6 of the 8 speeds are divisible by 3
                     (from `floor_of_leaveOneOut_imprimitive` at `k0 = 6`);
* `e2_prime_dvd9`    the per-prime contract: `lemma7Check 8 p = true` and `ML v < 1/9` give `p ∣ v i`.

Nothing here uses `native_decide`, `sorry` or a new axiom.  Hypothesis `LRC7` is the statement of
`EightRunnersReal.eight_runners_unconditional_real`, carried as a hypothesis.
-/

import LRSpectrumFull.RoomA4_rosenfeld
import LRSpectrumFull.LRCFourRunnersCore

namespace LRSpectrumFull.NineSound

open LRSpectrumFull

/-- **LRC7 (hypothesis).** LRC for seven speeds (eight runners), the shape of `ih` at `k₀ = 6`. -/
def LRC7 : Prop :=
  ∀ u : Fin (6 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((6 : ℝ) + 2) ≤ ML u

/-- A primitive counterexample for nine runners (eight speeds). -/
def IsCE9 (v : Fin 8 → ℤ) : Prop :=
  (∀ i, 0 < v i) ∧ Finset.univ.gcd v = 1 ∧ ML v < 1 / 9

/-- the number of speeds divisible by 3 -/
def threeCount (v : Fin 8 → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (3 : ℤ) ∣ v i)).card

/-- Folding a residue mod `9p` into `[1, 9p/2]`; divisibility by 3 of the fold implies that of the
speed because `3 ∣ 9p`. -/
theorem fold_facts9 (p : ℕ) (hp0 : 0 < p) (a : ℤ) (ha : 0 < a) (hna : ¬ (p : ℤ) ∣ a) :
    ∃ f : ℕ, 1 ≤ f ∧ f ≤ 9 * p / 2 ∧ f % p ≠ 0 ∧ (f % 3 = 0 → (3 : ℤ) ∣ a) ∧
      (((9 * p : ℕ) : ℤ) ∣ a - (f : ℤ) ∨ ((9 * p : ℕ) : ℤ) ∣ a + (f : ℤ)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg ha.le).symm⟩
  have hnp : ¬ p ∣ n := fun h => hna (by exact_mod_cast h)
  have hdm : 9 * p * (n / (9 * p)) + n % (9 * p) = n := Nat.div_add_mod n (9 * p)
  have hrlt : n % (9 * p) < 9 * p := Nat.mod_lt n (by omega)
  generalize n % (9 * p) = r at hdm hrlt
  generalize n / (9 * p) = d at hdm
  have hpr : ¬ p ∣ r := fun h => hnp (by
    rw [← hdm]; exact dvd_add (Dvd.dvd.mul_right (Dvd.intro_left 9 rfl) d) h)
  have hr0 : r ≠ 0 := fun h => hpr (by rw [h]; exact dvd_zero p)
  obtain ⟨m, hm⟩ : ∃ m, n = 9 * m + r := ⟨p * d, by rw [← hdm]; ring⟩
  by_cases hle : r ≤ 9 * p / 2
  · refine ⟨r, by omega, hle, fun h => hpr (Nat.dvd_of_mod_eq_zero h), fun h3 => ?_, Or.inl ?_⟩
    · have : n % 3 = 0 := by omega
      exact_mod_cast Nat.dvd_of_mod_eq_zero this
    · exact ⟨(d : ℤ), by rw [← hdm]; push_cast; ring⟩
  · refine ⟨9 * p - r, by omega, by omega, ?_, fun h3 => ?_, Or.inr ?_⟩
    · intro h
      apply hpr
      have h1 : p ∣ 9 * p - r := Nat.dvd_of_mod_eq_zero h
      exact (Nat.dvd_add_right h1).mp (by rw [Nat.sub_add_cancel hrlt.le]; exact Dvd.intro_left 9 rfl)
    · have : n % 3 = 0 := by omega
      exact_mod_cast Nat.dvd_of_mod_eq_zero this
    · refine ⟨(d : ℤ) + 1, ?_⟩
      rw [← hdm, Nat.cast_sub hrlt.le]
      push_cast; ring

/-- An uncovered `j` gives distance at least `1/9`. -/
theorem nid_ge_of_uncovered9 (p j f : ℕ) (hp : 0 < p)
    (h : 9 * p ≤ 9 * min (j * f % (9 * p)) (9 * p - j * f % (9 * p))) :
    (1 : ℝ) / 9 ≤ nearestIntDist (((j : ℤ) : ℝ) * ((f : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ)) := by
  have hq : 0 < 9 * p := by omega
  by_contra hlt
  push Not at hlt
  rw [show ((j : ℤ) : ℝ) * ((f : ℤ) : ℝ) = (((j * f : ℕ) : ℤ) : ℝ) by push_cast; ring] at hlt
  rw [nearestIntDist_div_lt_iff _ _ hq] at hlt
  rw [← Int.natCast_mod] at hlt
  have hrlt : j * f % (9 * p) < 9 * p := Nat.mod_lt _ hq
  generalize j * f % (9 * p) = r at hlt hrlt h
  have h1 : 9 * p ≤ 9 * r := by omega
  have h2 : 9 * p + 9 * r ≤ 9 * (9 * p) := by omega
  have h1R : (9 : ℝ) * p ≤ 9 * (r : ℝ) := by exact_mod_cast h1
  have h2R : (9 : ℝ) * p + 9 * (r : ℝ) ≤ 9 * (9 * p) := by exact_mod_cast h2
  simp only [Int.cast_natCast] at hlt
  push_cast at hlt
  rcases min_lt_iff.mp hlt with h3 | h3 <;> linarith

theorem admissible_mem9 (p x : ℕ) :
    x ∈ admissible 8 p ↔ (1 ≤ x ∧ x ≤ 9 * p / 2 ∧ x % p ≠ 0) := by
  simp only [admissible, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨b, by omega, c⟩
  · rintro ⟨a, b, c⟩; exact ⟨by omega, a, c⟩

/-- the side condition at `k = 8` is exactly "at most 6 multiples of 3": the only prime dividing
`k + 1 = 9` is 3, and `k - 2 = 6` -/
theorem sideOK_eight (V : List ℕ) :
    sideOK 8 V = decide ((V.filter (fun v => v % 3 == 0)).length ≤ 6) := by
  have hfilt : ((List.range (8 + 2)).filter
      (fun l => 2 ≤ l && (8 + 1) % l == 0 && Nat.Prime l)) = [3] := by decide
  unfold sideOK
  rw [hfilt]
  simp

/-- the eight padding classes: below `p`, prime to `p`, prime to 3 -/
theorem padding9 (p : ℕ) (h11 : 11 < p) :
    ∀ x ∈ ({1, 2, 4, 5, 7, 8, 10, 11} : Finset ℕ),
      1 ≤ x ∧ x ≤ 9 * p / 2 ∧ x % p ≠ 0 ∧ x % 3 ≠ 0 := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by norm_num, by omega, fun h => ?_, by norm_num⟩ <;>
    have hd := Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero h) <;>
    omega

/-! ## The divisor-complete step -/

/-- **E4 at k = 8.**  With LRC for seven speeds, a primitive counterexample has every leave-one-out
gcd equal to 1. -/
theorem e4_leaveOneOut9 (h7 : LRC7) (v : Fin 8 → ℤ) (hce : IsCE9 v) (l : Fin 8) :
    Finset.univ.gcd (fun j : Fin 7 => v (l.succAbove j)) = 1 := by
  by_contra hl
  have h := RoomA4Rosenfeld.floor_of_leaveOneOut_imprimitive 6 (by norm_num) h7 v hce.1 hce.2.1 l hl
  have h2 := hce.2.2
  norm_num at h
  linarith

/-- **The divisor-complete step.**  At most 6 of the 8 speeds of a primitive counterexample are
divisible by 3: seven or more would leave at most one speed outside, and the leave-one-out family
at that index (or the whole family) would have gcd divisible by 3. -/
theorem e4_three9 (h7 : LRC7) (v : Fin 8 → ℤ) (hce : IsCE9 v) : threeCount v ≤ 6 := by
  by_contra hgt
  push Not at hgt
  have hex : ∃ l : Fin 8, ∀ i, i ≠ l → (3 : ℤ) ∣ v i := by
    by_contra hno
    push Not at hno
    obtain ⟨i0, -, h0⟩ := hno 0
    obtain ⟨i1, h01, h1⟩ := hno i0
    have hsub : Finset.univ.filter (fun i => (3 : ℤ) ∣ v i) ⊆ (Finset.univ.erase i0).erase i1 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => by subst h; exact h1 hi, fun h => by subst h; exact h0 hi⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [h01]), Finset.card_erase_of_mem (Finset.mem_univ _)]
      at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    unfold threeCount at hgt
    omega
  obtain ⟨l, hl⟩ := hex
  have hg := e4_leaveOneOut9 h7 v hce l
  have h3 : (3 : ℤ) ∣ Finset.univ.gcd (fun j : Fin 7 => v (l.succAbove j)) :=
    Finset.dvd_gcd (fun j _ => hl _ (Fin.succAbove_ne l j))
  rw [hg] at h3
  norm_num at h3

/-! ## The per-prime contract at the odd modulus -/

/-- **E2 at k = 8 (odd modulus 9p).**  Reduce `v` mod `q = 9p`, fold `r ↦ min r (q - r)` into
`[1, 9p/2]`, pad to eight distinct admissible classes (padding keeps the side condition because
only the prime 3 divides `9`, and enlarges the covered set), apply `lemma7Check 8 p`, and transport
the uncovered `j` back with `nid_congr_mod`. -/
theorem e2_prime_dvd9 (p : ℕ) (h11 : 11 < p) (hchk : lemma7Check 8 p = true)
    (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) (hpar : threeCount v ≤ 6) (hML : ML v < 1 / 9) :
    ∃ i, (p : ℤ) ∣ v i := by
  classical
  by_contra hno
  push Not at hno
  have hp0 : 0 < p := by omega
  choose f hf1 hf4 hfp hf3 hfc using fun i => fold_facts9 p hp0 (v i) (hv i) (hno i)
  set O : Finset ℕ := {1, 2, 4, 5, 7, 8, 10, 11} with hOdef
  have hO := padding9 p h11
  set T0 : Finset ℕ := Finset.univ.image f with hT0def
  have hT0 : T0.card ≤ 8 := Finset.card_image_le.trans (by simp)
  have hOc : O.card = 8 := by rw [hOdef]; rfl
  obtain ⟨T, hT0T, hTU, hTc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : T0 ⊆ T0 ∪ O) hT0
    (hOc ▸ Finset.card_le_card Finset.subset_union_right)
  have hTadm : ∀ x ∈ T, x ∈ admissible 8 p := by
    intro x hx
    rw [admissible_mem9]
    rcases Finset.mem_union.mp (hTU hx) with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨hf1 i, hf4 i, hfp i⟩
    · exact ⟨(hO x h).1, (hO x h).2.1, (hO x h).2.2.1⟩
  have hTthree : (T.filter (fun x => x % 3 = 0)).card ≤ 6 := by
    have hsub : T.filter (fun x => x % 3 = 0) ⊆
        (Finset.univ.filter (fun i => (3 : ℤ) ∣ v i)).image f := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases Finset.mem_union.mp (hTU hx.1) with h | h
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf3 i hx.2⟩, rfl⟩
      · have := (hO x h).2.2.2; omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hpar)
  have hLnd : (admissible 8 p).Nodup := List.nodup_range.filter _
  set V := (admissible 8 p).filter (fun x => decide (x ∈ T)) with hVdef
  have hVnd : V.Nodup := hLnd.filter _
  have hVtf : V.toFinset = T := by
    ext x
    simp only [hVdef, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hTadm x h, h⟩⟩
  have hVlen : V.length = 8 := by
    rw [← List.toFinset_card_of_nodup hVnd, hVtf, hTc]
  have hVmem : V ∈ tuples 8 p := List.mem_sublistsLen.mpr ⟨List.filter_sublist, hVlen⟩
  have hside : sideOK 8 V = true := by
    rw [sideOK_eight, decide_eq_true_eq]
    have hnd3 : (V.filter (fun v => v % 3 == 0)).Nodup := hVnd.filter _
    rw [← List.toFinset_card_of_nodup hnd3]
    have hE : (V.filter (fun v => v % 3 == 0)).toFinset = T.filter (fun x => x % 3 = 0) := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, beq_iff_eq]
      rw [← List.mem_toFinset, hVtf]
    rw [hE]
    exact hTthree
  have hall := List.all_eq_true.mp hchk V hVmem
  rw [hside, Bool.true_and] at hall
  have hcw : coversWindow 8 p V = false := by simpa using hall
  rw [← Bool.not_eq_true, coversWindow, List.all_eq_true] at hcw
  push Not at hcw
  obtain ⟨j, -, hj⟩ := hcw
  have hunc : ∀ i, 9 * p ≤ 9 * min (j * f i % (9 * p)) (9 * p - j * f i % (9 * p)) := by
    intro i
    have hfi : f i ∈ V := by
      rw [hVdef, List.mem_filter, decide_eq_true_eq]
      have hT : f i ∈ T := hT0T (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨hTadm _ hT, hT⟩
    have hnc : ¬ coversAt 8 p j (f i) = true := fun hc =>
      hj (List.any_eq_true.mpr ⟨f i, hfi, hc⟩)
    simp only [coversAt, decide_eq_true_eq, show (8 : ℕ) + 1 = 9 from rfl] at hnc
    omega
  have hgap : (1 : ℝ) / 9 ≤ gap v (((j : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ)) := by
    apply le_gap
    intro i
    rw [show (v i : ℝ) * (((j : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ))
        = ((j : ℤ) : ℝ) * (v i : ℝ) / ((9 * p : ℕ) : ℝ) by ring]
    rcases hfc i with h | h
    · rw [nid_congr_mod (v i) (f i) (9 * p) (by omega) j h]
      exact nid_ge_of_uncovered9 p j (f i) hp0 (hunc i)
    · have h' : ((9 * p : ℕ) : ℤ) ∣ v i - (-(f i : ℤ)) := by rw [sub_neg_eq_add]; exact h
      rw [nid_congr_mod (v i) (-(f i : ℤ)) (9 * p) (by omega) j h']
      rw [show ((j : ℤ) : ℝ) * (((-(f i : ℤ)) : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ)
          = -(((j : ℤ) : ℝ) * ((f i : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ)) by push_cast; ring,
        nearestIntDist_neg]
      exact nid_ge_of_uncovered9 p j (f i) hp0 (hunc i)
  have := gap_le_ML v (((j : ℤ) : ℝ) / ((9 * p : ℕ) : ℝ))
  linarith

end LRSpectrumFull.NineSound
