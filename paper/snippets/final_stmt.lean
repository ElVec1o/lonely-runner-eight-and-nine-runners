/-- **Nine runners (all 36 primes closed by generated modules).**  The only hypothesis is `LRC7`. -/
theorem nine_runners_final (h7 : LRC7) (v : Fin 8 → ℤ) (hv : ∀ i, 0 < v i) : 1 / 9 ≤ ML v :=
