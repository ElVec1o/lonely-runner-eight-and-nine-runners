/-
# Nine runners, soundness part 1c: soundness of the bound-prune record (tag 3)

`NineProbe.Check` replays a certificate tree with Nat bit operations.  A record `3 t n v_1 .. v_n`
(`tailOK`) cuts a branch: with the per-class counters `cu` (16-bit fields, field `x` the number of
uncovered times covered by the class `x`), the uncovered count `nu` and the available mask `av`,
it asserts that every available class outside the exception set `T = {v_i}` has counter at most `t`,
every `v_i` has counter at least `t`, and `∑_T cnt + (r - n) t < nu`.  Then no set of at most `r`
available classes covers the uncovered times.

This file proves that statement for the checker as written (`tailOK`, `readT`, `allLe` of
`NineProbe.Check`, imported unchanged), in the style of `EightV4.leaf_false`:

* `readT_sound`, `tailOK_sound`   what a successful read of the record means;
* `allLe_sound`                    the SWAR comparison `allLe` (a `+ (32767 - t) * ones` trick on
                                   15-bit fields) means "every selected field is at most `t`";
* `boundLeaf_false`                the cut is sound: under the counter invariant (`cu` is the exact
                                   spread sum of the per-class counts) and `nu ≤ |U|`, no
                                   `Z ⊆ av ∩ [0, W]` with `|Z| ≤ r` covers `U`.

The covering relation `cov` is an arbitrary decidable relation (the level semantics supply it);
the only facts used about it are that covering classes are tracked (`≤ W`) and the counter
invariant.  The generic leaf lemma `EightV4.uniform_bound_no_cover` is imported unchanged.
Also here: a small concrete control (a record that must be accepted, two corrupted ones that must
be rejected, by `decide`).

No `native_decide`, no `sorry`, no axiom.
-/

import LRSpectrumFull.EightCheckSound
import LRSpectrumFull.NineProbe.Check

namespace LRSpectrumFull.NineSound

open LRSpectrumFull.NineProbe Finset

/-! ## Bridges: the checker primitives of `NineProbe` are definitionally those of `EightV4` -/

theorem ltN_eq9 (a b : ℕ) : ltN a b = decide (a < b) := EightV4.ltN_eq a b
theorem beq_eq9 (a b : ℕ) : Nat.beq a b = decide (a = b) := EightV4.beq_eq_decide a b
theorem ble_eq9 (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := EightV4.ble_eq_decide a b
theorem fld_eq9 (x v : ℕ) : fld x v = x / 2 ^ (16 * v) % 2 ^ 16 := EightV4.fld_eq x v
theorem testBit_clr9 (x m i : ℕ) : (clr x m).testBit i = (x.testBit i && !m.testBit i) :=
  EightV4.testBit_clr x m i
theorem sbit_eq9 (v : ℕ) : sbit v = 2 ^ (16 * v) := EightV4.sbit_eq v
theorem testBit_fld9 (x v s : ℕ) (hs : s < 16) : x.testBit (16 * v + s) = (fld x v).testBit s :=
  EightV4.testBit_fld x v s hs
theorem fld_sum9 (N : ℕ) (f : ℕ → ℕ) (hf : ∀ v < N, f v < 2 ^ 16) (v : ℕ) :
    fld (∑ w ∈ range N, f w * 2 ^ (16 * w)) v = if v < N then f v else 0 :=
  EightV4.fld_sum N f hf v

/-- bit `16 v` of a spread mask -/
def bitS (x v : ℕ) : Bool := x.testBit (16 * v)

theorem bitS_eq9 (x v : ℕ) : bitS x v = x.testBit (16 * v) := rfl

theorem bitS_clr_sbit (x c v : ℕ) : bitS (clr x (sbit c)) v = (bitS x v && !decide (v = c)) := by
  unfold bitS
  rw [testBit_clr9, sbit_eq9, Nat.testBit_two_pow]
  congr 2
  rw [decide_eq_decide]; omega

/-! ## The `allLe` comparison -/

/-- **`allLe` semantics.** -/
theorem allLe_sound (X : Ctx) (hones : X.ones = ∑ v ∈ range (X.W + 1), 1 * 2 ^ (16 * v))
    (L : ℕ) (ℓ : ℕ → ℕ) (hL : L = ∑ v ∈ range (X.W + 1), ℓ v * 2 ^ (16 * v))
    (hℓ : ∀ v, ℓ v < 2 ^ 15) (M t : ℕ) (h : allLe X L M t = true) :
    ∀ v < X.W + 1, bitS M v = true → ℓ v ≤ t := by
  intro v hv hM
  unfold allLe at h
  rw [Bool.and_eq_true, ltN_eq9, beq_eq9] at h
  obtain ⟨h1, h2⟩ := h
  have ht : t < 32768 := of_decide_eq_true h1
  have h0 : (L + (32767 - t) * X.ones) &&& (M <<< 15) = 0 := of_decide_eq_true h2
  have hsum : L + (32767 - t) * X.ones =
      ∑ w ∈ range (X.W + 1), (ℓ w + (32767 - t)) * 2 ^ (16 * w) := by
    rw [hL, hones, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _; ring
  have hb := congrArg (fun x => x.testBit (16 * v + 15)) h0
  simp only [Nat.testBit_and, Nat.zero_testBit] at hb
  rw [Nat.testBit_shiftLeft, show 16 * v + 15 - 15 = 16 * v by omega, ← bitS_eq9, hM] at hb
  simp only [ge_iff_le, show 15 ≤ 16 * v + 15 by omega, decide_true, Bool.and_true] at hb
  rw [hsum, testBit_fld9 _ _ _ (by norm_num),
    fld_sum9 _ _ (fun w _ => by have := hℓ w; omega), if_pos hv,
    Nat.testBit_eq_decide_div_mod_eq] at hb
  have := hℓ v
  simp at hb
  omega

/-! ## Reading the record -/

theorem readT_sound (C : ℕ → ℕ) (L t : ℕ) : ∀ n pv s M pos s' M' pos',
    readT C L t n pv s M pos = some (s', M', pos') →
    ∃ T : Finset ℕ, T.card = n ∧ (∀ v ∈ T, pv < v) ∧ (∀ v ∈ T, t ≤ fld L v) ∧
      s' = s + ∑ v ∈ T, fld L v ∧ ∀ v, bitS M' v = (bitS M v && decide (v ∉ T))
  | 0, pv, s, M, pos, s', M', pos', h => by
    simp only [readT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
  | n + 1, pv, s, M, pos, s', M', pos', h => by
    rw [readT] at h
    cases hc : (ltN pv (rd C pos) && Nat.ble t (fld L (rd C pos)))
    · rw [hc] at h; exact absurd h (by simp)
    · rw [hc] at h
      rw [Bool.and_eq_true, ltN_eq9, ble_eq9] at hc
      have h1 : pv < rd C pos := of_decide_eq_true hc.1
      have h2 : t ≤ fld L (rd C pos) := of_decide_eq_true hc.2
      obtain ⟨T, hTc, hTp, hTt, hs, hM⟩ := readT_sound C L t n _ _ _ _ s' M' pos' h
      set v := rd C pos
      have hvT : v ∉ T := fun hv => by have := hTp v hv; omega
      refine ⟨insert v T, by rw [Finset.card_insert_of_notMem hvT, hTc], ?_, ?_, ?_, ?_⟩
      · intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h1
        · have := hTp w hw; omega
      · intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h2
        · exact hTt w hw
      · rw [hs, Finset.sum_insert hvT]; show s + fld L v + _ = _; ring
      · intro w
        rw [hM w, bitS_clr_sbit]
        by_cases hw : w = v
        · subst hw; simp
        · simp [hw]

theorem tailOK_sound (X : Ctx) (C : ℕ → ℕ) (L B av r pos pos' : ℕ)
    (h : tailOK X C L B av r pos = some pos') :
    ∃ T : Finset ℕ, ∃ t M, T.card ≤ r ∧ (∀ v ∈ T, t ≤ fld L v) ∧
      ∑ v ∈ T, fld L v + (r - T.card) * t < B ∧ allLe X L M t = true ∧
      ∀ v, bitS M v = (bitS av v && decide (v ∉ T)) := by
  unfold tailOK at h
  dsimp only at h
  cases hn : Nat.ble (rd C (Nat.succ pos)) r
  · rw [hn] at h; exact absurd h (by simp)
  · rw [hn] at h
    simp only [cond_true] at h
    split at h
    · exact absurd h (by simp)
    · rename_i s M p2 hr
      cases hc : (allLe X L M (rd C pos) &&
          ltN (Nat.add s (Nat.mul (Nat.sub r (rd C (Nat.succ pos))) (rd C pos))) B)
      · rw [hc] at h; exact absurd h (by simp)
      · rw [Bool.and_eq_true, ltN_eq9] at hc
        obtain ⟨T, hTc, -, hTt, hs, hM⟩ := readT_sound C L _ _ _ _ _ _ _ _ _ hr
        have hnr : rd C (Nat.succ pos) ≤ r := by
          rw [ble_eq9] at hn; exact of_decide_eq_true hn
        refine ⟨T, rd C pos, M, by omega, hTt, ?_, hc.1, hM⟩
        have h' : s + (r - rd C (Nat.succ pos)) * rd C pos < B := of_decide_eq_true hc.2
        rw [hs, ← hTc, Nat.zero_add] at h'; exact h'

/-! ## The cut is sound -/

/-- **Bound-prune soundness.**  Let `U` be the set of uncovered times, `cov j v` the covering
relation, `cu` the exact spread sum of the per-class counts, `nu ≤ |U|`.  If the record read by
`tailOK` at `pos` is accepted, no set `Z` of at most `r` tracked classes allowed by `av` covers
every time of `U`. -/
theorem boundLeaf_false (X : Ctx) (C : ℕ → ℕ) (cov : ℕ → ℕ → Prop)
    [∀ j v, Decidable (cov j v)] (U : Finset ℕ) (hU : U.card < 2 ^ 15)
    (hcovW : ∀ j v, cov j v → v < X.W + 1)
    (hones : X.ones = ∑ v ∈ range (X.W + 1), 1 * 2 ^ (16 * v))
    (cu nu av r pos pos' : ℕ)
    (hcu : cu = ∑ v ∈ range (X.W + 1), (U.filter (fun j => cov j v)).card * 2 ^ (16 * v))
    (hnu : nu ≤ U.card)
    (h : tailOK X C cu nu av r pos = some pos')
    (Z : Finset ℕ) (hZW : ∀ v ∈ Z, v < X.W + 1) (hZb : ∀ v ∈ Z, bitS av v = true)
    (hZr : Z.card ≤ r) (hcov : ∀ j ∈ U, ∃ v ∈ Z, cov j v) : False := by
  obtain ⟨T, t, M, hTr, hTt, hlt, hall, hM⟩ := tailOK_sound X C cu nu av r pos pos' h
  have hℓ : ∀ v, (U.filter (fun j => cov j v)).card < 2 ^ 15 := fun v =>
    lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hU
  have hfl : ∀ v, fld cu v = (U.filter (fun j => cov j v)).card := by
    intro v
    rw [hcu, fld_sum9 _ _ (fun w _ => lt_of_lt_of_le (hℓ w) (by norm_num)) v]
    split_ifs with hv
    · rfl
    · have : U.filter (fun j => cov j v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _ hc
        exact hv (hcovW j v hc)
      rw [this]; rfl
  have hle := allLe_sound X hones cu (fun v => (U.filter (fun j => cov j v)).card) hcu hℓ M t hall
  refine EightV4.uniform_bound_no_cover cov U Z T r t hTr ?_ ?_ ?_ Z (subset_refl _) hZr hcov
  · intro v hv hvT
    apply hle v (hZW v hv)
    rw [hM v, hZb v hv]; simp [hvT]
  · intro v hv; rw [← hfl v]; exact hTt v hv
  · simp only [hfl] at hlt; omega

/-! ## A concrete control: one accepted record, two corrupted ones rejected -/

/-- classes `0..3`, counters `(0, 3, 5, 1)`, allowed `{1, 2, 3}` -/
def ctlX : Ctx where
  lvl := 0
  W := 3
  full := 0
  adm := 0
  m3 := 0
  ones := 1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48
  lowp := 0
  lowT := 0
  row := fun _ => (0, 0, 0, 0)
  cbJ := fun _ => 0
  cntF := fun _ _ => 0

def ctlCu : ℕ := 3 * 2 ^ 16 + 5 * 2 ^ 32 + 1 * 2 ^ 48
def ctlAv : ℕ := 2 ^ 16 + 2 ^ 32 + 2 ^ 48

/-- record `t = 3, n = 1, T = {2}`: blob 0 holds the fields `3, 1, 2` -/
def ctlC (t : ℕ) : ℕ → ℕ := fun i => if i = 0 then t + 1 * 2 ^ 16 + 2 * 2 ^ 32 else 0

/-- accepted: `5 + (1 - 1) * 3 = 5 < 7` and every class outside `T` has counter `≤ 3` -/
theorem ctl_accept : tailOK ctlX (ctlC 3) ctlCu 7 ctlAv 1 0 = some 3 := by
  decide +kernel

/-- the bound `5 < 5` is false -/
theorem ctl_reject_bound : tailOK ctlX (ctlC 3) ctlCu 5 ctlAv 1 0 = none := by
  decide +kernel

/-- threshold `t = 2`: the allowed class `1` outside `T` has counter `3 > 2` -/
theorem ctl_reject_threshold : tailOK ctlX (ctlC 2) ctlCu 7 ctlAv 1 0 = none := by
  decide +kernel

end LRSpectrumFull.NineSound
