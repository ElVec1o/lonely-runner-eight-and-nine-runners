/-- LRC for eight runners, per-prime checks from the staged kernel proofs. -/
theorem eight_runners_unconditional_real (v : Fin 7 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 8 ≤ ML v :=
