/-
# Nine runners, soundness part 2c: the item masks and the slot count derived from the items

The checker `NineProbe.Check` keeps the classes of a node in SPREAD masks (bit `16 x` for the class `x`)
and builds the masks of the pinned items by Nat arithmetic: `spc` (a popcount by multiplication with
`ones`), `lowB`/`clr` (isolate and clear the lowest set bit), `orRows` (union of table rows over the set
bits of a mask, at most 16 bits), `rootSt` (root state of a tree from its descriptor).  This file proves
that this arithmetic computes the intended class predicates:

* `spc9_spreadOf`         `spc X (spreadOf A) = |A|`;
* `spreadOf_lor/land/clr` union, intersection, difference of spread masks are the masks of the set
                          operations;
* `spreadOf_lowB`         `lowB (spreadOf U)` is the bit of the least class, `clr` removes it;
* `orRows_spec`           `orRows` over a spread mask of at most `f` classes is the spread mask of the
                          union of the per-class sets (the fuel 16 is enough because an accepted root
                          has `|items| <= 8`);
* `rootSt_masks`          for `TableOK9 X i p` (`i >= 2`) and items `Icm` (classes mod `p`), `Ict`
                          (classes mod `3p`) the root state has `mp` = spread of the admissible classes
                          `y` with `y = +-c (mod p)` for some `c` in `Icm`, `mq`, `mf` the same mod `3p`
                          for the non-multiples / multiples of 3 of `Ict`, `c3` = the number of multiples
                          of 3 of `Ict`, and the free-pick count `fr`;
* `checkRootN_count`      an accepted root has `|Icm| + |Ict| + fr = 8` (the slot count).

No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.StatementG
import LRSpectrumFull.NineSound.Bound
import LRSpectrumFull.NineSound.Replay

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

/-! ## Spread masks: cleanliness, extensionality, set operations -/

def Clean16 (x : ℕ) : Prop := ∀ i, x.testBit i = true → ∃ v, i = 16 * v

theorem clean16_spreadOf (A : Finset ℕ) : Clean16 (EightV4.spreadOf A) := by
  intro i hi
  rw [EightV4.testBit_spreadOf] at hi
  have := of_decide_eq_true hi
  obtain ⟨v, _, hv⟩ := this
  exact ⟨v, hv.symm⟩

theorem ext16 (x y : ℕ) (hx : Clean16 x) (hy : Clean16 y)
    (h : ∀ v, x.testBit (16 * v) = y.testBit (16 * v)) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : ∃ v, i = 16 * v
  · obtain ⟨v, rfl⟩ := hi; exact h v
  · have h1 : x.testBit i = false := by
      cases hh : x.testBit i
      · rfl
      · exact absurd (hx i hh) hi
    have h2 : y.testBit i = false := by
      cases hh : y.testBit i
      · rfl
      · exact absurd (hy i hh) hi
    rw [h1, h2]

theorem tb_sp (A : Finset ℕ) (v : ℕ) : (EightV4.spreadOf A).testBit (16 * v) = decide (v ∈ A) := by
  have := EightV4.bitS_spreadOf A v
  rw [EightV4.bitS_eq] at this
  exact this

theorem spreadOf_lor (A B : Finset ℕ) :
    Nat.lor (EightV4.spreadOf A) (EightV4.spreadOf B) = EightV4.spreadOf (A ∪ B) := by
  apply ext16
  · intro i hi
    have h : (EightV4.spreadOf A).testBit i = true ∨ (EightV4.spreadOf B).testBit i = true := by
      have := Nat.testBit_lor (EightV4.spreadOf A) (EightV4.spreadOf B) i
      have h2 : (Nat.lor (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit i = true := hi
      simp only [Nat.lor_eq] at h2
      rw [this] at h2; simpa using h2
    rcases h with h | h
    · exact clean16_spreadOf A i h
    · exact clean16_spreadOf B i h
  · exact clean16_spreadOf _
  · intro v
    have e : (Nat.lor (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit (16 * v) =
        ((EightV4.spreadOf A).testBit (16 * v) || (EightV4.spreadOf B).testBit (16 * v)) :=
      Nat.testBit_lor _ _ _
    rw [e, tb_sp, tb_sp, tb_sp]
    simp

theorem spreadOf_land (A B : Finset ℕ) :
    Nat.land (EightV4.spreadOf A) (EightV4.spreadOf B) = EightV4.spreadOf (A ∩ B) := by
  apply ext16
  · intro i hi
    have e := Nat.testBit_land (EightV4.spreadOf A) (EightV4.spreadOf B) i
    have h2 : (Nat.land (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit i = true := hi
    simp only [Nat.land_eq] at h2
    rw [e] at h2
    exact clean16_spreadOf A i (by simpa using (Bool.and_eq_true_iff.mp h2).1)
  · exact clean16_spreadOf _
  · intro v
    have e : (Nat.land (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit (16 * v) =
        ((EightV4.spreadOf A).testBit (16 * v) && (EightV4.spreadOf B).testBit (16 * v)) :=
      Nat.testBit_land _ _ _
    rw [e, tb_sp, tb_sp, tb_sp]
    simp

theorem spreadOf_clr (A B : Finset ℕ) :
    clr (EightV4.spreadOf A) (EightV4.spreadOf B) = EightV4.spreadOf (A \ B) := by
  apply ext16
  · intro i hi
    have e : (clr (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit i =
        ((EightV4.spreadOf A).testBit i && !(EightV4.spreadOf B).testBit i) :=
      EightV4.testBit_clr _ _ _
    rw [e] at hi
    exact clean16_spreadOf A i (by simpa using (Bool.and_eq_true_iff.mp hi).1)
  · exact clean16_spreadOf _
  · intro v
    have e : (clr (EightV4.spreadOf A) (EightV4.spreadOf B)).testBit (16 * v) =
        ((EightV4.spreadOf A).testBit (16 * v) && !(EightV4.spreadOf B).testBit (16 * v)) :=
      EightV4.testBit_clr _ _ _
    rw [e, tb_sp, tb_sp, tb_sp]
    by_cases h1 : v ∈ A <;> by_cases h2 : v ∈ B <;> simp [h1, h2]

theorem spreadOf_empty : EightV4.spreadOf (∅ : Finset ℕ) = 0 := by simp [EightV4.spreadOf]

/-- the lowest set bit of a spread mask is the bit of the least class, and `clr` removes it -/
theorem spreadOf_lowB (U : Finset ℕ) (hU : U.Nonempty) :
    lowB (EightV4.spreadOf U) = 2 ^ (16 * U.min' hU) ∧
    clr (EightV4.spreadOf U) (2 ^ (16 * U.min' hU)) = EightV4.spreadOf (U.erase (U.min' hU)) := by
  have hmin := U.min'_mem hU
  have hbit : (EightV4.spreadOf U).testBit (16 * U.min' hU) = true := by
    rw [tb_sp]; simp [hmin]
  have hne : EightV4.spreadOf U ≠ 0 := by
    intro h0; rw [h0] at hbit; simp at hbit
  obtain ⟨k, hk, hkt, hkl⟩ := lowB_spec _ hne
  have hk16 : ∃ v ∈ U, 16 * v = k := by
    have := (EightV4.testBit_spreadOf U k) ▸ hkt
    exact of_decide_eq_true this
  obtain ⟨v, hv, rfl⟩ := hk16
  have hvm : U.min' hU = v := by
    apply le_antisymm
    · exact U.min'_le v hv
    · by_contra hlt
      have := hkl (16 * U.min' hU) (by omega)
      rw [hbit] at this; exact absurd this (by simp)
  rw [hvm] at *
  refine ⟨hk, ?_⟩
  have e2 : (2 : ℕ) ^ (16 * v) = EightV4.spreadOf {v} := by simp [EightV4.spreadOf]
  rw [e2, spreadOf_clr]
  congr 1
  ext x; simp [and_comm]

/-! ## The popcount `spc` -/

theorem spc9_spreadOf (X : Ctx) (hones : X.ones = EightV4.spreadOf (range (X.W + 1)))
    (hW : X.W + 1 < 2 ^ 16) (A : Finset ℕ) (hA : A ⊆ range (X.W + 1)) :
    spc X (EightV4.spreadOf A) = A.card := by
  have hN : ∀ v ∈ A, v < X.W + 1 := fun v hv => mem_range.mp (hA hv)
  show fld (EightV4.spreadOf A * X.ones) X.W = A.card
  have hon : X.ones = ∑ v ∈ range (X.W + 1), 1 * 2 ^ (16 * v) := by
    rw [hones]; simp [EightV4.spreadOf]
  rw [EightV4.spreadOf_range A (X.W + 1) hN, hon, EightV4.mul_ones]
  have hcard : ∑ a ∈ range (X.W + 1), (if a ∈ A then 1 else 0) = A.card := by
    simp only [Finset.sum_boole, Nat.cast_id]; congr 1; ext v; simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hN v h, h⟩⟩
  have hle : ∀ c, (∑ a ∈ range (X.W + 1), if a ≤ c ∧ c < a + (X.W + 1) then (if a ∈ A then 1 else 0) else 0)
      ≤ X.W + 1 := by
    intro c
    calc _ ≤ ∑ a ∈ range (X.W + 1), 1 := Finset.sum_le_sum (fun a _ => by split <;> (try split) <;> omega)
      _ = X.W + 1 := by simp
  rw [fld_sum9 _ _ (fun c _ => lt_of_le_of_lt (hle c) (by omega)), if_pos (by omega)]
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro a ha; rw [mem_range] at ha
  rw [if_pos ⟨by omega, by omega⟩]

/-! ## `orRows` -/

/-- `orRows` over the spread mask of at most `f` classes is the spread mask of the union -/
theorem orRows_spec (X : Ctx) (sel : ℕ × ℕ × ℕ × ℕ → ℕ) (S : ℕ → Finset ℕ) :
    ∀ (f : ℕ) (U : Finset ℕ) (acc : ℕ), U.card ≤ f →
      (∀ x ∈ U, sel (X.row (2 ^ (16 * x))) = EightV4.spreadOf (S x)) →
      orRows X sel f (EightV4.spreadOf U) acc =
        Nat.lor acc (EightV4.spreadOf (U.biUnion S)) := by
  intro f
  induction f with
  | zero =>
    intro U acc hc _
    have : U = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    simp [orRows, spreadOf_empty]
  | succ f ih =>
    intro U acc hc hsel
    by_cases hU : U = ∅
    · subst hU
      simp [orRows, spreadOf_empty]
    · have hUn : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
      obtain ⟨hlow, hclr⟩ := spreadOf_lowB U hUn
      have hne : EightV4.spreadOf U ≠ 0 := by
        intro h0
        have hb : (EightV4.spreadOf U).testBit (16 * U.min' hUn) = true := by
          rw [tb_sp]; simp [U.min'_mem hUn]
        rw [h0] at hb; simp at hb
      have hb : Nat.beq (EightV4.spreadOf U) 0 = false := beq_zero_false _ hne
      unfold orRows
      simp only [hb, cond_false]
      rw [hlow, hclr]
      have hx := U.min'_mem hUn
      have hcard : (U.erase (U.min' hUn)).card ≤ f := by
        rw [Finset.card_erase_of_mem hx]; omega
      rw [ih _ _ hcard (fun y hy => hsel y (Finset.mem_of_mem_erase hy)), hsel _ hx]
      have hbi : U.biUnion S = S (U.min' hUn) ∪ (U.erase (U.min' hUn)).biUnion S := by
        conv_lhs => rw [← Finset.insert_erase hx]
        rw [Finset.biUnion_insert]
      rw [hbi, ← spreadOf_lor]
      exact Nat.lor_assoc _ _ _

/-! ## Root state masks -/

def liftSet (M p q : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (AdmC M p).filter (fun y => ∃ c ∈ U, PM q c y)

theorem admC_sub_range (M p : ℕ) : AdmC M p ⊆ range (M / 2 + 1) := by
  intro x hx
  simp only [AdmC, Win, mem_filter, mem_Icc] at hx
  simp only [mem_range]; omega

/-- **Item masks of the root.**  For a level-2 context (`i = 2`), items `Icm` (classes mod `p`) and `Ict`
(classes mod `3p`), the root state computed by the checker has the intended class predicates. -/
theorem rootSt_masks (X : Ctx) (p : ℕ) (hT : TableOK9g X 2 p) (hW : X.W + 1 < 2 ^ 16)
    (Icm Ict : Finset ℕ) (hI : Icm ⊆ AdmC (9 * p) p) (hJ : Ict ⊆ AdmC (9 * p) p)
    (h1 : Icm.card ≤ 16) (h2 : (Ict.filter (fun c => ¬ 3 ∣ c)).card ≤ 16)
    (h3 : (Ict.filter (fun c => 3 ∣ c)).card ≤ 16) (fr : ℕ) :
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).mp =
        EightV4.spreadOf (liftSet (9 * p) p p Icm) ∧
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).mq =
        EightV4.spreadOf (liftSet (9 * p) p (3 * p) (Ict.filter (fun c => ¬ 3 ∣ c))) ∧
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).mf =
        EightV4.spreadOf (liftSet (9 * p) p (3 * p) (Ict.filter (fun c => 3 ∣ c))) ∧
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).c3 = (Ict.filter (fun c => 3 ∣ c)).card ∧
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).fr = fr ∧
    (rootSt X (EightV4.spreadOf Icm) (EightV4.spreadOf Ict) fr).r = 8 := by
  have hT' := hT
  obtain ⟨hlvl, hWd, hfull, hadm, hm3, hones, hlowp, hlowT, hrow, hcb, hcnt⟩ := hT
  have hlv : lvlMult 2 = 9 := by simp [lvlMult]
  rw [hlv] at hrow hm3 hWd
  have hm3' : X.m3 = EightV4.spreadOf ((Win (9 * p)).filter (fun x => x % 3 = 0)) := by
    rw [hm3]; simp
  -- the row selectors
  have hrowP : ∀ x ∈ AdmC (9 * p) p, (X.row (2 ^ (16 * x))).2.2.1 = EightV4.spreadOf ((AdmC (9 * p) p).filter (fun y => PM p x y)) := by
    intro x hx; rw [hrow x hx]; simp
  have hrowT : ∀ x ∈ AdmC (9 * p) p, (X.row (2 ^ (16 * x))).2.2.2 = EightV4.spreadOf ((AdmC (9 * p) p).filter (fun y => PM (3 * p) x y)) := by
    intro x hx; rw [hrow x hx]; simp
  have hdiv : ∀ c, c % 3 = 0 ↔ 3 ∣ c := fun c => Nat.dvd_iff_mod_eq_zero.symm
  have hm3s : EightV4.spreadOf ((Win (9 * p)).filter (fun x => x % 3 = 0)) =
      EightV4.spreadOf ((Win (9 * p)).filter (fun x => 3 ∣ x)) := by
    congr 1; ext x; simp [hdiv]
  have hF : Nat.land (EightV4.spreadOf Ict) X.m3 = EightV4.spreadOf (Ict.filter (fun c => 3 ∣ c)) := by
    rw [hm3', hm3s, spreadOf_land]
    congr 1; ext x
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨hx, hx2, hx3⟩; exact ⟨hx, hx3⟩
    · rintro ⟨hx, hx3⟩; exact ⟨hx, (mem_filter.mp (hJ hx)).1, hx3⟩
  have hN : clr (EightV4.spreadOf Ict) X.m3 = EightV4.spreadOf (Ict.filter (fun c => ¬ 3 ∣ c)) := by
    rw [hm3', hm3s, spreadOf_clr]
    congr 1; ext x
    simp only [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨hx, hn⟩; exact ⟨hx, fun h3 => hn ⟨(mem_filter.mp (hJ hx)).1, h3⟩⟩
    · rintro ⟨hx, hn⟩; exact ⟨hx, fun ⟨_, h3⟩ => hn h3⟩
  have hFsub : Ict.filter (fun c => 3 ∣ c) ⊆ AdmC (9 * p) p := fun x hx => hJ (mem_filter.mp hx).1
  have hNsub : Ict.filter (fun c => ¬ 3 ∣ c) ⊆ AdmC (9 * p) p := fun x hx => hJ (mem_filter.mp hx).1
  have e0 : ∀ x, Nat.lor 0 x = x := fun x => Nat.zero_or x
  unfold rootSt
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals simp only [hF, hN]
  · rw [orRows_spec X (fun t => t.2.2.1) (fun x => (AdmC (9 * p) p).filter (fun y => PM p x y)) 16 Icm 0
      h1 (fun x hx => hrowP x (hI hx))]
    simp only [e0]
    congr 1; ext y
    simp only [liftSet, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨c, hc, hy, hpm⟩; exact ⟨hy, c, hc, hpm⟩
    · rintro ⟨hy, c, hc, hpm⟩; exact ⟨c, hc, hy, hpm⟩
  · rw [orRows_spec X (fun t => t.2.2.2) (fun x => (AdmC (9 * p) p).filter (fun y => PM (3 * p) x y)) 16 _ 0
      h2 (fun x hx => hrowT x (hNsub hx))]
    simp only [e0]
    congr 1; ext y
    simp only [liftSet, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨c, hc, hy, hpm⟩; exact ⟨hy, c, hc, hpm⟩
    · rintro ⟨hy, c, hc, hpm⟩; exact ⟨c, hc, hy, hpm⟩
  · rw [orRows_spec X (fun t => t.2.2.2) (fun x => (AdmC (9 * p) p).filter (fun y => PM (3 * p) x y)) 16 _ 0
      h3 (fun x hx => hrowT x (hFsub hx))]
    simp only [e0]
    congr 1; ext y
    simp only [liftSet, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨c, hc, hy, hpm⟩; exact ⟨hy, c, hc, hpm⟩
    · rintro ⟨hy, c, hc, hpm⟩; exact ⟨c, hc, hy, hpm⟩
  · have hWd' : X.W = 9 * p / 2 := hWd
    exact spc9_spreadOf X hones hW _ (fun x hx => by
      have := admC_sub_range (9 * p) p (hFsub hx); rwa [← hWd'] at this)

/-- **Slot count.**  An accepted root has `|Icm| + |Ict| + fr = 8`. -/
theorem checkRootN_count (X : Ctx) (p : ℕ) (hT : TableOK9g X 2 p) (hW : X.W + 1 < 2 ^ 16)
    (Icm Ict : Finset ℕ) (hI : Icm ⊆ AdmC (9 * p) p) (hJ : Ict ⊆ AdmC (9 * p) p) (fr : ℕ)
    (h : Nat.beq (Nat.add (Nat.add (spc X (EightV4.spreadOf Icm)) (spc X (EightV4.spreadOf Ict))) fr)
      (nat_lit 8) = true) :
    Icm.card + Ict.card + fr = 8 := by
  obtain ⟨hlvl, hWd, hfull, hadm, hm3, hones, hlowp, hlowT, hrow, hcb, hcnt⟩ := hT
  have hlv : lvlMult 2 = 9 := by simp [lvlMult]
  rw [hlv] at hWd
  have hWd' : X.W = 9 * p / 2 := hWd
  rw [spc9_spreadOf X hones hW Icm (fun x hx => by
        have := admC_sub_range (9 * p) p (hI hx); rwa [← hWd'] at this),
      spc9_spreadOf X hones hW Ict (fun x hx => by
        have := admC_sub_range (9 * p) p (hJ hx); rwa [← hWd'] at this)] at h
  have := Nat.eq_of_beq_eq_true h
  simpa [Nat.add_eq] using this

end LRSpectrumFull.NineSound
