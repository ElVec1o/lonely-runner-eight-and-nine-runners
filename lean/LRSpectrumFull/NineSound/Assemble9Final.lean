import LRSpectrumFull.NineSound.Assemble9
import LRSpectrumFull.EightRunnersReal

/-!
# Nine runners, unconditional (bridge from the eight-runner theorem)

NOT in any aggregator and NOT built by `lake build`: it imports
* `LRSpectrumFull.EightRunnersReal` (needs the staged oleans `E8Stage/P<p>/Asm.olean` of the 27
  per-prime kernel proofs in the staging directory `repro/eight/stage/work/olean`), and
* `LRSpectrumFull.NineSound.Assemble9` (needs the restored `G<p>` archives).
Build only with `repro/assemble_final.sh --run` (raw `lean`).

`EightRunnersReal.eight_runners_unconditional_real` is stated for `v : Fin 7 → ℤ` with positive
(not necessarily distinct, not necessarily coprime) entries and conclusion `1 / 8 ≤ ML v`.
`NineSound.LRC7` is `∀ u : Fin (6 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((6 : ℝ) + 2) ≤ ML u`;
`Fin (6 + 1)` and `Fin 7` are definitionally equal and `(6 : ℝ) + 2 = 8` by `norm_num`.
-/

namespace LRSpectrumFull.NineSound.Plan9.Assemble9Final
open LRSpectrumFull LRSpectrumFull.NineSound

/-- The hypothesis of `Assemble9.nine_runners_final`, from the eight-runner theorem. -/
theorem lrc7_of_eight : LRC7 := by
  intro u hu
  have h := LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real u hu
  have e : (1 : ℝ) / ((6 : ℝ) + 2) = 1 / 8 := by norm_num
  rw [e]
  exact h

/-- **Nine runners, no hypothesis.** -/
theorem nine_runners_unconditional :
    ∀ v : Fin 8 → ℤ, (∀ i, 0 < v i) → 1 / 9 ≤ ML v :=
  fun v hv => Assemble9.nine_runners_final lrc7_of_eight v hv

end LRSpectrumFull.NineSound.Plan9.Assemble9Final

#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9Final.lrc7_of_eight
#print axioms LRSpectrumFull.NineSound.Plan9.Assemble9Final.nine_runners_unconditional
#check @LRSpectrumFull.NineSound.Plan9.Assemble9Final.nine_runners_unconditional
