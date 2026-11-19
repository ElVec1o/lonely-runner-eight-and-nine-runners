/-
# Nine runners, soundness part 6 (B5): chunked validation of the generated tables

`TabCheck.TableFin9g X i p` is checked for the real tables of a prime by `decide +kernel`; for p = 179 a single
`decide` at level 1 exceeded 8 GB (part 5 note).  The expensive clauses are the two universally quantified ones
(`row` for all admissible classes `x`, `cbJ` for all times `j`), each of cost about the window size.  Here they
are cut into chunks that are separate theorems (the kernel releases its caches between theorems):

* `RowChunk X i p lo hi`   the row clause for the classes `x` in `[lo, hi)` prime to `p`;
* `CbChunk X i p lo hi`    the coverer-mask clause for the times `j` in `[lo, hi)`;
* `RowsUpTo`, `CbUpTo`     the cumulative statements, and `rows_step`, `cb_step` chain consecutive chunks;
* `ScalFin9`               the eight scalar clauses (checked as one `decide`);
* `tableFin9g_of_parts`    scalar clauses plus the two cumulative statements up to `X.W + 1` give `TableFin9g`;
* `cfRef_eq`               the light reference counter tree `NineProbe.cfRef` (in the generated contexts:
                           `cntF := cfRef cbJ (W+1) 1 (W+1)`) is the `cfRef` of `TabCheck`;
* `tableOK9g_of'`          `TableFin9g` plus the definitional `cntF` clause give `TableOK9g` (the statement
                           consumed by `Check9SoundGb`).
No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.NineSound.TabCheck
import LRSpectrumFull.NineProbe.Tabs

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe

/-- the light `cfRef` (generated contexts) equals the `cfRef` of `TabCheck` -/
theorem cfRef_eq (cb : ℕ → ℕ) : ∀ (f lo hi u acc : ℕ),
    LRSpectrumFull.NineProbe.cfRef cb f lo hi u acc = LRSpectrumFull.NineSound.cfRef cb f lo hi u acc := by
  intro f
  induction f with
  | zero => intro lo hi u acc; rfl
  | succ f ih =>
    intro lo hi u acc
    have hm : LRSpectrumFull.NineProbe.maskR lo hi = LRSpectrumFull.NineSound.maskR lo hi := rfl
    simp only [LRSpectrumFull.NineProbe.cfRef, LRSpectrumFull.NineSound.cfRef, ih, hm]

/-- the row clause of `TableFin9g` for the class `x` -/
def RowOK (X : Ctx) (i p x : ℕ) : Prop :=
  X.row (2 ^ (16 * x)) =
      (x, EightV4.compactOf ((Win (lvlMult i * p)).filter (fun j => covM (lvlMult i * p) j x)),
        (if 1 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM p x y)) else 0),
        (if 2 ≤ i then EightV4.spreadOf ((AdmC (lvlMult i * p) p).filter (fun y => PM (3 * p) x y))
          else 0))

/-- the coverer-mask clause of `TableFin9g` for the time `j` -/
def CbOK (X : Ctx) (i p j : ℕ) : Prop :=
  X.cbJ j = EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => covM (lvlMult i * p) j x))

instance (X : Ctx) (i p x : ℕ) : Decidable (RowOK X i p x) := by unfold RowOK; infer_instance
instance (X : Ctx) (i p j : ℕ) : Decidable (CbOK X i p j) := by unfold CbOK; infer_instance

/-- one chunk of the row clause: the classes `x` in `[lo, hi)` prime to `p` -/
def RowChunk (X : Ctx) (i p lo hi : ℕ) : Prop :=
  ∀ x ∈ Finset.Ico lo hi, x % p ≠ 0 → RowOK X i p x

/-- one chunk of the coverer-mask clause: the times `j` in `[lo, hi)` -/
def CbChunk (X : Ctx) (i p lo hi : ℕ) : Prop := ∀ j ∈ Finset.Ico lo hi, CbOK X i p j

instance (X : Ctx) (i p lo hi : ℕ) : Decidable (RowChunk X i p lo hi) := by unfold RowChunk; infer_instance
instance (X : Ctx) (i p lo hi : ℕ) : Decidable (CbChunk X i p lo hi) := by unfold CbChunk; infer_instance

/-- cumulative: every class `1 <= x < n` prime to `p` has its row -/
def RowsUpTo (X : Ctx) (i p n : ℕ) : Prop := ∀ x, 1 ≤ x → x < n → x % p ≠ 0 → RowOK X i p x
/-- cumulative: every time `1 <= j < n` has its coverer mask -/
def CbUpTo (X : Ctx) (i p n : ℕ) : Prop := ∀ j, 1 ≤ j → j < n → CbOK X i p j

theorem rows_base (X : Ctx) (i p : ℕ) : RowsUpTo X i p 1 := fun _ h1 h2 _ => absurd h2 (by omega)
theorem cb_base (X : Ctx) (i p : ℕ) : CbUpTo X i p 1 := fun _ h1 h2 => absurd h2 (by omega)

theorem rows_step {X : Ctx} {i p n m : ℕ} (h : RowsUpTo X i p n) (hc : RowChunk X i p n m) :
    RowsUpTo X i p m := by
  intro x h1 h2 h3
  by_cases hx : x < n
  · exact h x h1 hx h3
  · exact hc x (Finset.mem_Ico.2 ⟨by omega, h2⟩) h3

theorem cb_step {X : Ctx} {i p n m : ℕ} (h : CbUpTo X i p n) (hc : CbChunk X i p n m) :
    CbUpTo X i p m := by
  intro j h1 h2
  by_cases hj : j < n
  · exact h j h1 hj
  · exact hc j (Finset.mem_Ico.2 ⟨by omega, h2⟩)

/-- the eight scalar clauses of `TableFin9g` -/
def ScalFin9 (X : Ctx) (i p : ℕ) : Prop :=
  X.lvl = i ∧ X.W = (lvlMult i * p) / 2 ∧
  X.full = EightV4.compactOf (Win (lvlMult i * p)) ∧
  X.adm = EightV4.spreadOf (AdmC (lvlMult i * p) p) ∧
  X.m3 = (if i = 0 then 0
      else EightV4.spreadOf ((Win (lvlMult i * p)).filter (fun x => x % 3 = 0))) ∧
  X.ones = EightV4.spreadOf (Finset.range (X.W + 1)) ∧
  X.lowp = EightV4.spreadOf (Finset.Icc 1 ((p - 1) / 2)) ∧
  X.lowT = EightV4.spreadOf (Finset.Icc 1 (min ((lvlMult i * p) / 2) ((3 * p - 1) / 2)))

instance (X : Ctx) (i p : ℕ) : Decidable (ScalFin9 X i p) := by unfold ScalFin9; infer_instance

/-- the finite part of the table statement from its three parts -/
theorem tableFin9g_of_parts (X : Ctx) (i p : ℕ) (hs : ScalFin9 X i p)
    (hr : RowsUpTo X i p (X.W + 1)) (hc : CbUpTo X i p (X.W + 1)) : TableFin9g X i p := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hs
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, ?_, ?_⟩
  · intro x hx
    simp only [AdmC, Win, Finset.mem_filter, Finset.mem_Icc] at hx
    exact hr x hx.1.1 (by omega) hx.2
  · intro j hj
    simp only [Win, Finset.mem_Icc] at hj
    exact hc j hj.1 (by omega)

/-- `TableOK9g` from the finite part and the definitional counter clause of the generated context -/
theorem tableOK9g_of' (X : Ctx) (i p : ℕ) (hfin : TableFin9g X i p)
    (hcf : ∀ u acc, X.cntF u acc =
      LRSpectrumFull.NineProbe.cfRef X.cbJ (X.W + 1) 1 (X.W + 1) u acc) : TableOK9g X i p :=
  tableOK9g_of X i p hfin (fun u acc => by rw [hcf, cfRef_eq])

/-- everything at once: scalar clauses, the two cumulative statements, the definitional counter clause -/
theorem tableOK9g_of_parts (X : Ctx) (i p : ℕ) (hs : ScalFin9 X i p)
    (hr : RowsUpTo X i p (X.W + 1)) (hc : CbUpTo X i p (X.W + 1))
    (hcf : ∀ u acc, X.cntF u acc =
      LRSpectrumFull.NineProbe.cfRef X.cbJ (X.W + 1) 1 (X.W + 1) u acc) : TableOK9g X i p :=
  tableOK9g_of' X i p (tableFin9g_of_parts X i p hs hr hc) hcf

end LRSpectrumFull.NineSound
