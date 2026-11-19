/-
# Nine runners, soundness part 6 (B5): the counter clause with a constant fuel

Measured in this part: with `cntF := cfRef cbJ (W+1) 1 (W+1)` (fuel `W+1`, as in `TabCheck`) the kernel pays
O(W) per call (structural recursion on a literal of size `W+1`), which made the replay of the p = 179 tasks about
6 times slower (level 0) and about 50 times slower (level 2) than the unrolled tree.  The tree has depth
`log2 W`, so a fuel of 13 suffices for every `W < 4096`.  Here:

* `cfRefL_spec`          for `hi - lo <= 2^f` the light `cfRef` with fuel `f + 1` is the counter sum;
* `tableOK9g_of_partsF`  the table statement from the scalar part, the two cumulative chunk statements, the
                         bound `W < 4096` and the definitional clause `cntF = cfRef cbJ 13 1 (W+1)`.
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.TabChunk

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

theorem cfRefL_spec (cb : ℕ → ℕ) : ∀ (f lo hi u acc : ℕ), hi - lo ≤ 2 ^ f →
    LRSpectrumFull.NineProbe.cfRef cb (f + 1) lo hi u acc =
      acc + ∑ j ∈ Ico lo hi, (if u.testBit j = true then cb j else 0) := by
  intro f
  induction f with
  | zero =>
    intro lo hi u acc h
    rw [cfRef_eq]
    simp only [pow_zero] at h
    by_cases hlh : hi ≤ lo
    · have he : Ico lo hi = ∅ := by ext x; simp; omega
      have hz : Nat.land u (maskR lo hi) = 0 := by rw [maskR_zero lo hi hlh]; simp
      have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = true := by rw [hz]; rfl
      simp only [LRSpectrumFull.NineSound.cfRef, hb, cond_true, he, Finset.sum_empty, add_zero]
    · have hhi : hi = lo + 1 := by omega
      subst hhi
      by_cases hz : Nat.land u (maskR lo (lo + 1)) = 0
      · have hb : Nat.beq (Nat.land u (maskR lo (lo + 1))) 0 = true := by rw [hz]; rfl
        have hbit : u.testBit lo = false := by
          have := land_mask_zero u lo (lo + 1) hz lo (le_refl _) (by omega)
          exact this
        simp only [LRSpectrumFull.NineSound.cfRef, hb, cond_true, Nat.Ico_succ_singleton,
          Finset.sum_singleton, hbit]
        simp
      · have hb : Nat.beq (Nat.land u (maskR lo (lo + 1))) 0 = false := beq_zero_false _ hz
        have hbit : u.testBit lo = true := by
          by_contra hn
          apply hz
          apply land_mask_ne
          intro j h3 h4
          have : j = lo := by omega
          subst this; simpa using hn
        have hb1 : Nat.beq (lo + 1 - lo) 1 = true := by
          have : lo + 1 - lo = 1 := by omega
          rw [this]; rfl
        simp only [LRSpectrumFull.NineSound.cfRef, hb, hb1, cond_false, cond_true]
        rw [Nat.Ico_succ_singleton, Finset.sum_singleton, if_pos hbit]
  | succ f ih =>
    intro lo hi u acc h
    rw [cfRef_eq]
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    by_cases hlh : hi ≤ lo
    · have he : Ico lo hi = ∅ := by ext x; simp; omega
      have hz : Nat.land u (maskR lo hi) = 0 := by rw [maskR_zero lo hi hlh]; simp
      have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = true := by rw [hz]; rfl
      simp only [LRSpectrumFull.NineSound.cfRef, hb, cond_true, he, Finset.sum_empty, add_zero]
    · by_cases hz : Nat.land u (maskR lo hi) = 0
      · have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = true := by rw [hz]; rfl
        have hs : ∑ j ∈ Ico lo hi, (if u.testBit j = true then cb j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [mem_Ico] at hj
          rw [land_mask_zero u lo hi hz j hj.1 hj.2]; simp
        simp only [LRSpectrumFull.NineSound.cfRef, hb, cond_true, hs, add_zero]
      · have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = false := beq_zero_false _ hz
        by_cases h1 : hi - lo = 1
        · have hb1 : Nat.beq (hi - lo) 1 = true := by rw [h1]; rfl
          have hhi : hi = lo + 1 := by omega
          have hbit : u.testBit lo = true := by
            by_contra hn
            apply hz
            apply land_mask_ne
            intro j h3 h4
            have : j = lo := by omega
            subst this; simpa using hn
          subst hhi
          simp only [LRSpectrumFull.NineSound.cfRef, hb, hb1, cond_false, cond_true]
          rw [Nat.Ico_succ_singleton, Finset.sum_singleton, if_pos hbit]
        · have hb1 : Nat.beq (hi - lo) 1 = false := by
            rw [EightV4.beq_eq_decide]; simp [h1]
          rw [LRSpectrumFull.NineSound.cfRef, hb, hb1]
          simp only [cond_false]
          have hmid1 : lo < (lo + hi) / 2 := by omega
          have hmid2 : (lo + hi) / 2 < hi := by omega
          have e1 := ih ((lo + hi) / 2) hi u acc (by omega)
          rw [cfRef_eq] at e1
          rw [e1]
          have e2 := ih lo ((lo + hi) / 2) u (acc + ∑ j ∈ Ico ((lo + hi) / 2) hi, (if u.testBit j = true then cb j else 0)) (by omega)
          rw [cfRef_eq] at e2
          rw [e2]
          rw [← Finset.sum_Ico_consecutive _ hmid1.le hmid2.le]
          ring

/-- `TableOK9g` from the parts, with the counter clause as generated (`cfRef cbJ 13 1 (W+1)`) -/
theorem tableOK9g_of_partsF (X : Ctx) (i p : ℕ) (hs : ScalFin9 X i p)
    (hr : RowsUpTo X i p (X.W + 1)) (hc : CbUpTo X i p (X.W + 1)) (hW : X.W < 4096)
    (hcf : ∀ u acc, X.cntF u acc = LRSpectrumFull.NineProbe.cfRef X.cbJ 13 1 (X.W + 1) u acc) :
    TableOK9g X i p := by
  apply tableOK9g_of X i p (tableFin9g_of_parts X i p hs hr hc)
  intro u acc
  rw [hcf, cfRefL_spec X.cbJ 12 1 (X.W + 1) u acc (by norm_num; omega),
    cfRef_spec X.cbJ (X.W + 1) 1 (X.W + 1) u acc (by omega)]

end LRSpectrumFull.NineSound
