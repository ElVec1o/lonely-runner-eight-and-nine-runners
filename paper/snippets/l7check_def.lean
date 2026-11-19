def lemma7Check (k p : ℕ) : Bool :=
  (tuples k p).all (fun V => !(sideOK k V && coversWindow k p V))
