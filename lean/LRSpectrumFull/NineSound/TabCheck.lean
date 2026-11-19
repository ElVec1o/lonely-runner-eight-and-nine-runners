/-
# Nine runners, soundness part 2d: validation of the generated tables (`TableOK9g`)

`TableOK9g X i p` (Statement.lean) says what the generated context of level `i` must encode.  Its first ten
clauses are finite checks (`TableFin9g`, decidable: kernel `decide`); the last clause (`cntF`, the counter
sum over a set of times, for ALL `u`) is not decidable.  The generator emits `cntF` as a balanced tree of
`bif (u &&& mask) = 0 then acc else ...` nodes (`cf` trees of `gen_probe.rs`).  Here:

* `maskR`, `cfRef`          the reference tree, same shape, defined once and generically;
* `cfRef_spec`              `cfRef cb f lo hi u acc = acc + sum of cb j over the set bits j of u in [lo, hi)`;
* `tableOK9g_of`             `TableFin9g X i p` and `X.cntF = cfRef X.cbJ ..` give `TableOK9g X i p`.

For a concrete table the equality `X.cntF u acc = cfRef X.cbJ .. u acc` is a definitional unfolding
(`rfl`), and `TableFin9g` is `decide +kernel`; see `Tab13.lean`.  No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.StatementG
import LRSpectrumFull.NineSound.Replay

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

def maskR (lo hi : ℕ) : ℕ := 2 ^ hi - 2 ^ lo

/-- reference counter tree (the shape of the generated `cf` trees) -/
def cfRef (cb : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | f + 1, lo, hi, u, acc =>
    bif Nat.beq (Nat.land u (maskR lo hi)) 0 then acc
    else bif Nat.beq (hi - lo) 1 then acc + cb lo
    else cfRef cb f lo ((lo + hi) / 2) u (cfRef cb f ((lo + hi) / 2) hi u acc)

theorem maskR_eq (lo hi : ℕ) (h : lo ≤ hi) : maskR lo hi = 2 ^ lo * (2 ^ (hi - lo) - 1) + 0 := by
  unfold maskR
  have h2 : 2 ^ hi = 2 ^ lo * 2 ^ (hi - lo) := by rw [← pow_add]; congr 1; omega
  rw [h2, Nat.mul_sub_one]; simp

theorem testBit_maskR (lo hi j : ℕ) (h : lo ≤ hi) :
    (maskR lo hi).testBit j = decide (lo ≤ j ∧ j < hi) := by
  rw [maskR_eq lo hi h, EightV4.testBit_two_pow_mul_add lo _ 0 j (by positivity)]
  by_cases hj : j < lo
  · simp [hj]
  · rw [if_neg hj, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_decide]; omega

theorem maskR_zero (lo hi : ℕ) (h : hi ≤ lo) : maskR lo hi = 0 := by
  unfold maskR
  exact Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right (by norm_num) h)

theorem land_mask_zero (u lo hi : ℕ) (h : Nat.land u (maskR lo hi) = 0) :
    ∀ j, lo ≤ j → j < hi → u.testBit j = false := by
  intro j h1 h2
  have e : (Nat.land u (maskR lo hi)).testBit j = (u.testBit j && (maskR lo hi).testBit j) :=
    Nat.testBit_land _ _ _
  rw [h, testBit_maskR lo hi j (by omega)] at e
  simp only [Nat.zero_testBit, h1, h2, and_self, decide_true, Bool.and_true] at e
  exact e.symm

theorem land_mask_ne (u lo hi : ℕ) (h : ∀ j, lo ≤ j → j < hi → u.testBit j = false) :
    Nat.land u (maskR lo hi) = 0 := by
  by_cases hl : lo ≤ hi
  · apply Nat.eq_of_testBit_eq
    intro j
    have e : (Nat.land u (maskR lo hi)).testBit j = (u.testBit j && (maskR lo hi).testBit j) :=
      Nat.testBit_land _ _ _
    rw [e, testBit_maskR lo hi j hl, Nat.zero_testBit]
    by_cases hj : lo ≤ j ∧ j < hi
    · rw [h j hj.1 hj.2]; simp
    · simp [hj]
  · rw [maskR_zero lo hi (by omega)]; simp

/-- **Specification of the counter tree.** -/
theorem cfRef_spec (cb : ℕ → ℕ) :
    ∀ (f lo hi u acc : ℕ), hi - lo ≤ f →
      cfRef cb f lo hi u acc = acc + ∑ j ∈ Ico lo hi, (if u.testBit j = true then cb j else 0) := by
  intro f
  induction f with
  | zero =>
    intro lo hi u acc h
    have : Ico lo hi = ∅ := by ext x; simp; omega
    simp [cfRef, this]
  | succ f ih =>
    intro lo hi u acc h
    by_cases hlh : hi ≤ lo
    · have : Ico lo hi = ∅ := by ext x; simp; omega
      have hz : Nat.land u (maskR lo hi) = 0 := by rw [maskR_zero lo hi hlh]; simp
      have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = true := by rw [hz]; rfl
      simp only [cfRef, hb, cond_true, this, Finset.sum_empty, add_zero]
    · by_cases hz : Nat.land u (maskR lo hi) = 0
      · have hb : Nat.beq (Nat.land u (maskR lo hi)) 0 = true := by rw [hz]; rfl
        have hs : ∑ j ∈ Ico lo hi, (if u.testBit j = true then cb j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [mem_Ico] at hj
          rw [land_mask_zero u lo hi hz j hj.1 hj.2]; simp
        simp only [cfRef, hb, cond_true, hs, add_zero]
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
          simp only [cfRef, hb, hb1, cond_false, cond_true]
          rw [Nat.Ico_succ_singleton, Finset.sum_singleton, if_pos hbit]
        · have hb1 : Nat.beq (hi - lo) 1 = false := by
            rw [EightV4.beq_eq_decide]; simp [h1]
          simp only [cfRef, hb, hb1, cond_false]
          have hmid1 : lo < (lo + hi) / 2 := by omega
          have hmid2 : (lo + hi) / 2 < hi := by omega
          rw [ih _ _ _ _ (by omega), ih _ _ _ _ (by omega)]
          rw [← Finset.sum_Ico_consecutive _ hmid1.le hmid2.le]
          ring

theorem Icc_eq_Ico (n : ℕ) : Icc 1 n = Ico 1 (n + 1) := by
  ext x; simp only [mem_Icc, mem_Ico]; omega

/-- The finite part of `TableOK9g`: all clauses except `cntF` -/
def TableFin9g (X : Ctx) (i p : ℕ) : Prop :=
  X.lvl = i ∧ X.W = (lvlMult i * p) / 2 ∧
  X.full = EightV4.compactOf (Win (lvlMult i * p)) ∧
  X.adm = EightV4.spreadOf (AdmC (lvlMult i * p) p) ∧
  X.m3 = (if i = 0 then 0
      else EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => x % 3 = 0))) ∧
  X.ones = EightV4.spreadOf (Finset.range (X.W + 1)) ∧
  X.lowp = EightV4.spreadOf (Finset.Icc 1 ((p - 1) / 2)) ∧
  X.lowT = EightV4.spreadOf (Finset.Icc 1 (min ((lvlMult i * p) / 2) ((3 * p - 1) / 2))) ∧
  (∀ x ∈ AdmC (lvlMult i * p) p, X.row (2 ^ (16 * x)) =
      (x, EightV4.compactOf ((Win (lvlMult i * p)).filter (fun j => covM (lvlMult i * p) j x)),
        (if 1 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM p x y)) else 0),
        (if 2 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM (3 * p) x y))
          else 0))) ∧
  (∀ j ∈ Win (lvlMult i * p), X.cbJ j =
      EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => covM (lvlMult i * p) j x)))

instance (X : Ctx) (i p : ℕ) : Decidable (TableFin9g X i p) := by
  unfold TableFin9g; infer_instance

/-- **Table validation.**  The finite clauses plus the tree shape of `cntF` give `TableOK9g`. -/
theorem tableOK9g_of (X : Ctx) (i p : ℕ) (hfin : TableFin9g X i p)
    (hcf : ∀ u acc, X.cntF u acc = cfRef X.cbJ (X.W + 1) 1 (X.W + 1) u acc) : TableOK9g X i p := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hfin
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_⟩
  intro u acc _
  rw [hcf, cfRef_spec _ _ _ _ _ _ (by omega)]
  congr 1
  have hW : Win (lvlMult i * p) = Ico 1 (X.W + 1) := by
    unfold Win; rw [a2]; exact Icc_eq_Ico _
  rw [hW, Finset.sum_filter]

end LRSpectrumFull.NineSound
