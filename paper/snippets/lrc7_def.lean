def LRC7 : Prop :=
  ∀ u : Fin (6 + 1) → ℤ, (∀ i, 0 < u i) → 1 / ((6 : ℝ) + 2) ≤ ML u
