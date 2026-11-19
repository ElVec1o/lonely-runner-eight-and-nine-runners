theorem eight_runners_of (h6 : EightPlan.LRC6)
    (hchk : ∀ p ∈ EightPlan.rosenfeldS, lemma7Check 7 p = true)
    (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v := by
  refine EightPlan.e0_primitive (fun w hw hg => ?_) v hv
