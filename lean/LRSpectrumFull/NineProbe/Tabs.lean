/-
# Nine runners, part 6: light helpers for the generated per-prime tables

No Mathlib import (the generated data modules must stay cheap to import: about 0.9 s of start-up per module
in the S2 measurement).  Nothing here is a claim about the lonely runner conjecture.

* `maskR`, `cfRef`   the reference counter tree: `cfRef cb f lo hi u acc = acc + sum of cb j over the set bits j
                     of u in [lo, hi)` (the specification is `NineSound.cfRef_spec`; `NineSound.TabChunk` shows
                     that this definition equals the `NineSound.cfRef` of `TabCheck`).  The generated context
                     says `cntF := cfRef cbJ (W+1) 1 (W+1)`, so the counter clause of the table statement
                     needs no unrolled tree.
* `pf`, `pk`         packed tables: entry `k` of a blob holding `G` entries of `w` bits is
                     `(blob >> (w k)) mod 2^w`; `pk T w G x` reads entry `x` of the table whose blob `i` is `T i`.
-/

namespace LRSpectrumFull.NineProbe

def maskR (lo hi : Nat) : Nat := 2 ^ hi - 2 ^ lo

/-- reference counter tree (the shape of the old unrolled `cf` trees), defined once and generically -/
def cfRef (cb : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | f + 1, lo, hi, u, acc =>
    bif Nat.beq (Nat.land u (maskR lo hi)) 0 then acc
    else bif Nat.beq (hi - lo) 1 then acc + cb lo
    else cfRef cb f lo ((lo + hi) / 2) u (cfRef cb f ((lo + hi) / 2) hi u acc)

/-- field `k` of width `w` of `blob` -/
def pf (blob w k : Nat) : Nat := Nat.land (Nat.shiftRight blob (w * k)) (2 ^ w - 1)

/-- entry `x` of a packed table (`G` entries of `w` bits per blob, blob `i` is `T i`) -/
def pk (T : Nat → Nat) (w G x : Nat) : Nat := pf (T (x / G)) w (x % G)

end LRSpectrumFull.NineProbe
