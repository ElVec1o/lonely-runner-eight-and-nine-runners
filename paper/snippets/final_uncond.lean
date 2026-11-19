theorem nine_runners_unconditional :
    ∀ v : Fin 8 → ℤ, (∀ i, 0 < v i) → 1 / 9 ≤ ML v :=
