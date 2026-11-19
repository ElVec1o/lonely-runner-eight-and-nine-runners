theorem lrc7_of_eight : LRC7 := by
  intro u hu
  have h := LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real u hu
  have e : (1 : ℝ) / ((6 : ℝ) + 2) = 1 / 8 := by norm_num
  rw [e]
  exact h
