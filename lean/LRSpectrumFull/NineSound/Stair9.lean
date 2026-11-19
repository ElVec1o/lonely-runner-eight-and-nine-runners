/-
# Nine runners, part 7a: the staircase lemma `e5b_staircase`, extracted without the stubs of `EightMSS`

Lines 25 to 255 of `EightMSS.lean` copied VERBATIM (checked by `diff` against `sed -n 25,255p`), with
only the namespace changed.  `EightMSS` also contains `bridge31`, a declaration with an unfinished proof body (dead
end, not on any path); importing it would put an unfinished declaration into the olean closure of the nine-runner
assembly.  This module imports only `Mathlib` and `MaxLoneliness`.

`e5b_staircase`: for `v : Fin n → ℤ` positive with `gcd v = 1`, and `l ≥ 1` with `l ^ (n - 1) < ∑ v`, there
are an integer vector `z`, not parallel to `v`, and a rational `σ` with `|l * z i - σ * v i| ≤ 1` for every `i`.
Generic in `n` and `l`; the nine-runner use is `n = 8`, `l = 36`.
-/

import Mathlib
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull.NineSound.Stair9

open Finset

variable {n : ℕ} (v : Fin n → ℤ)

/-- Events: `(i, a)` with `a < v i`. -/
abbrev Ev := Σ i : Fin n, Fin (v i).toNat

/-- Time of an event. -/
def tau (e : Ev v) : ℚ := (2 * (e.2 : ℚ) + 1) / (2 * (v e.1 : ℚ))

/-- The staircase point just before event `e`. -/
def qpt (e : Ev v) (j : Fin n) : ℤ :=
  if j < e.1 then ⌊tau v e * v j + 1 / 2⌋ else ⌈tau v e * v j + 1 / 2⌉ - 1

variable {v}

lemma tau_mul_self (hv : ∀ i, 0 < v i) (e : Ev v) :
    tau v e * v e.1 + 1 / 2 = ((e.2 : ℕ) : ℚ) + 1 := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  unfold tau
  field_simp
  ring

lemma tau_pos (hv : ∀ i, 0 < v i) (e : Ev v) : 0 < tau v e := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  unfold tau
  positivity

lemma tau_lt_one (hv : ∀ i, 0 < v i) (e : Ev v) : tau v e < 1 := by
  have h : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  have ha : ((e.2 : ℕ) : ℤ) < v e.1 := by
    have := e.2.isLt
    omega
  have ha' : ((e.2 : ℕ) : ℚ) + 1 ≤ v e.1 := by exact_mod_cast ha
  unfold tau
  rw [div_lt_one (by positivity)]
  linarith

lemma qpt_self (hv : ∀ i, 0 < v i) (e : Ev v) : qpt v e e.1 = (e.2 : ℕ) := by
  unfold qpt
  rw [if_neg (lt_irrefl _), tau_mul_self hv]
  have : ⌈((e.2 : ℕ) : ℚ) + 1⌉ = ((e.2 : ℕ) : ℤ) + 1 := by
    rw [show ((e.2 : ℕ) : ℚ) + 1 = (((e.2 : ℕ) + 1 : ℤ) : ℚ) by push_cast; ring, Int.ceil_intCast]
  rw [this]; ring

lemma qpt_self_lt (hv : ∀ i, 0 < v i) (e : Ev v) : qpt v e e.1 < v e.1 := by
  rw [qpt_self hv]
  have := e.2.isLt
  omega

lemma qpt_eps (e : Ev v) (j : Fin n) : |(qpt v e j : ℚ) - tau v e * v j| ≤ 1 / 2 := by
  rw [abs_le]
  unfold qpt
  split_ifs
  · have h1 := Int.floor_le (tau v e * v j + 1 / 2)
    have h2 := Int.lt_floor_add_one (tau v e * v j + 1 / 2)
    constructor <;> linarith
  · have h1 := Int.le_ceil (tau v e * v j + 1 / 2)
    have h2 := Int.ceil_lt_add_one (tau v e * v j + 1 / 2)
    push_cast
    constructor <;> linarith

lemma qpt_nonneg (hv : ∀ i, 0 < v i) (e : Ev v) (j : Fin n) : 0 ≤ qpt v e j := by
  have ht := tau_pos hv e
  have hj : (0 : ℚ) < v j := by exact_mod_cast hv j
  have hx : 0 < tau v e * v j := mul_pos ht hj
  unfold qpt
  split_ifs
  · exact Int.floor_nonneg.mpr (by linarith)
  · have : (0 : ℤ) < ⌈tau v e * v j + 1 / 2⌉ := Int.ceil_pos.mpr (by linarith)
    omega

/-- Domination: a later event sees strictly more steps in the coordinate of an earlier one. -/
lemma qpt_dom (hv : ∀ i, 0 < v i) (e e' : Ev v)
    (h : tau v e < tau v e' ∨ (tau v e = tau v e' ∧ e.1 < e'.1)) :
    qpt v e e.1 < qpt v e' e.1 := by
  rw [qpt_self hv]
  have hi : (0 : ℚ) < v e.1 := by exact_mod_cast hv e.1
  have hle : tau v e ≤ tau v e' := by rcases h with h | h; exact h.le; exact h.1.le
  have hmono : tau v e * v e.1 ≤ tau v e' * v e.1 := mul_le_mul_of_nonneg_right hle hi.le
  have hs := tau_mul_self hv e
  unfold qpt
  split_ifs with hlt
  · have : ((e.2 : ℕ) : ℤ) + 1 ≤ ⌊tau v e' * v e.1 + 1 / 2⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    omega
  · have hstrict : tau v e < tau v e' := by
      rcases h with h | h
      · exact h
      · exact absurd h.2 hlt
    have hm : tau v e * v e.1 < tau v e' * v e.1 := mul_lt_mul_of_pos_right hstrict hi
    have : ((e.2 : ℕ) : ℤ) + 1 < ⌈tau v e' * v e.1 + 1 / 2⌉ := by
      rw [Int.lt_ceil]; push_cast; linarith
    omega

lemma qpt_inj (hv : ∀ i, 0 < v i) {e e' : Ev v} (hne : e ≠ e') : qpt v e ≠ qpt v e' := by
  intro heq
  rcases lt_trichotomy (tau v e) (tau v e') with h | h | h
  · have := qpt_dom hv e e' (Or.inl h); rw [heq] at this; exact lt_irrefl _ this
  · rcases lt_trichotomy e.1 e'.1 with hi | hi | hi
    · have := qpt_dom hv e e' (Or.inr ⟨h, hi⟩); rw [heq] at this; exact lt_irrefl _ this
    · apply hne
      obtain ⟨i, a⟩ := e
      obtain ⟨i', a'⟩ := e'
      simp only at hi
      subst hi
      have hvi : (0 : ℚ) < v i := by exact_mod_cast hv i
      unfold tau at h
      simp only at h
      rw [div_left_inj' (by positivity)] at h
      have : (a : ℕ) = a' := by exact_mod_cast (by linarith : ((a : ℕ) : ℚ) = a')
      rw [Fin.ext this]
    · have := qpt_dom hv e' e (Or.inr ⟨h.symm, hi⟩); rw [heq] at this; exact lt_irrefl _ this
  · have := qpt_dom hv e' e (Or.inl h); rw [heq] at this; exact lt_irrefl _ this

/-- `gcd v = 1` and `a ∣ c * v j` for all `j` give `a ∣ c`. -/
lemma dvd_of_dvd_mul_all (hg : Finset.univ.gcd v = 1) (a c : ℤ) (h : ∀ j, a ∣ c * v j) :
    a ∣ c := by
  have : a ∣ Finset.univ.gcd (fun j => c * v j) := Finset.dvd_gcd (fun j _ => h j)
  rw [Finset.gcd_mul_left, hg, mul_one] at this
  exact dvd_normalize_iff.mp this

/-- **E5b (staircase + pigeonhole).** -/
theorem e5b_staircase (hv : ∀ i, 0 < v i) (hg : Finset.univ.gcd v = 1) (l : ℕ) (hl : 0 < l)
    (hsum : (l : ℤ) ^ (n - 1) < ∑ i, v i) :
    ∃ z : Fin n → ℤ, ∃ σ : ℚ, (∃ a b, z a * v b ≠ z b * v a) ∧
      ∀ i, |(l : ℚ) * z i - σ * v i| ≤ 1 := by
  haveI : NeZero l := ⟨hl.ne'⟩
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hsum
  -- card of events
  have hcardE : (Fintype.card (Ev v) : ℤ) = ∑ i, v i := by
    rw [Fintype.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by simp [Fintype.card_fin, Int.toNat_of_nonneg (hv i).le])
  have hcard : Fintype.card (Fin n → ZMod l) < Fintype.card (Ev v × Fin l) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
    have h1 : ((l ^ (n - 1) : ℕ) : ℤ) < (Fintype.card (Ev v) : ℤ) := by
      rw [hcardE]; exact_mod_cast hsum
    have h2 : l ^ (n - 1) < Fintype.card (Ev v) := by exact_mod_cast h1
    have h3 : l ^ n = l ^ (n - 1) * l := by
      rw [← pow_succ]; congr 1; omega
    rw [h3]
    exact Nat.mul_lt_mul_of_pos_right h2 hl
  obtain ⟨⟨e, c⟩, ⟨e', c'⟩, hne, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Ev v × Fin l => fun j => ((qpt v p.1 j + (p.2 : ℤ) * v j : ℤ) : ZMod l)) hcard
  have hdvd : ∀ j, (l : ℤ) ∣ (qpt v e' j + (c' : ℤ) * v j) - (qpt v e j + (c : ℤ) * v j) :=
    fun j => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hcol j)
  -- the case e = e'
  by_cases hee : e = e'
  · exfalso
    subst hee
    have hcc : c ≠ c' := fun h => hne (by rw [h])
    have : (l : ℤ) ∣ ((c' : ℤ) - c) := by
      apply dvd_of_dvd_mul_all hg
      intro j
      have := hdvd j
      rwa [show qpt v e j + (c' : ℤ) * v j - (qpt v e j + (c : ℤ) * v j) = ((c' : ℤ) - c) * v j
        by ring] at this
    obtain ⟨k, hk⟩ := this
    have hc1 := c.isLt
    have hc2 := c'.isLt
    have hne' : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (l : ℤ) * k ≤ -l := by nlinarith
      omega
    · subst hk0; simp at hk; omega
    · have : (l : ℤ) ≤ l * k := by nlinarith
      omega
  -- the case e ≠ e'
  set d : Fin n → ℤ := fun j => qpt v e j - qpt v e' j with hd
  set z : Fin n → ℤ := fun j => (d j - ((c' : ℤ) - c) * v j) / l with hz
  have hlz : ∀ j, (l : ℤ) * z j = d j - ((c' : ℤ) - c) * v j := by
    intro j
    apply Int.mul_ediv_cancel'
    have := dvd_neg.mpr (hdvd j)
    convert this using 1
    simp only [hd]; ring
  refine ⟨z, tau v e - tau v e' - ((c' : ℚ) - c), ?_, ?_⟩
  · by_contra hpar
    push Not at hpar
    have hdpar : ∀ a b, d a * v b = d b * v a := by
      intro a b
      have ha := hlz a
      have hb := hlz b
      have hab := hpar a b
      have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      apply mul_left_cancel₀ hl0
      linear_combination -((l : ℤ) * v b) * ha + ((l : ℤ) * v a) * hb + ((l : ℤ) * l) * hab
    set i0 := e.1
    have hvi0 := hv i0
    have hdiv : v i0 ∣ d i0 := by
      apply dvd_of_dvd_mul_all hg
      intro j
      exact ⟨d j, by rw [hdpar i0 j]; ring⟩
    obtain ⟨s, hs⟩ := hdiv
    have hds : ∀ j, d j = s * v j := by
      intro j
      apply mul_left_cancel₀ hvi0.ne'
      linear_combination v j * hs - hdpar i0 j
    rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
    · -- q e' = q e - s v ≥ v at e'.1
      have h1 := hds e'.1
      have h2 := qpt_self_lt hv e'
      have h3 := qpt_nonneg hv e e'.1
      have h4 := hv e'.1
      simp only [hd] at h1
      nlinarith
    · apply qpt_inj hv hee
      funext j
      have := hds j
      simp only [hd, hs0, zero_mul] at this
      omega
    · have h1 := hds e.1
      have h2 := qpt_self_lt hv e
      have h3 := qpt_nonneg hv e' e.1
      have h4 := hv e.1
      simp only [hd] at h1
      nlinarith
  · intro i
    have h := hlz i
    have hq : ((l : ℤ) : ℚ) * (z i : ℚ) = ((d i - ((c' : ℤ) - c) * v i : ℤ) : ℚ) := by
      exact_mod_cast h
    push_cast at hq
    have e1 := qpt_eps e i
    have e2 := qpt_eps e' i
    rw [abs_le] at e1 e2 ⊢
    simp only [hd] at hq
    push_cast at hq
    constructor <;> linarith

end LRSpectrumFull.NineSound.Stair9
