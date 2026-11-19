/-
# Nine-runner cover-tree replay checker (kernel probe S2, K = 8, levels p, 3p, 9p)

PROBE ONLY (measurement of kernel cost per node).  No soundness theorem is proved here; the checker is
written in the style of `EightCheckV4` (Nat bit operations, incremental per-class counters, bound leaves
with a hint (t, T), certificate as packed Nat blobs read by a cursor) so that its measured cost carries over.
Nothing in this file is a claim about the lonely runner conjecture.

Representations.
* Times `j` (window `1 .. W`, `W = (M-1)/2`) live in COMPACT form (bit `j`).
* Classes `x` (same range) live in SPREAD form (bit `16 x`); counters `cu` are 16-bit fields at the same places:
  field `x` of `cu` is `|cov x ∩ unc|`.
* Tables are functions in the generated modules (balanced trees of row constants), keyed by the isolated
  spread bit of the class (`row`), or by the time (`cbJ`).
  `row b = (x, cov x, pcls x, tcls x)`: class number, covered times (compact), all classes congruent to `±x`
  mod `p` (spread), all classes congruent to `±x` mod `3p` (spread).
* Certificate: 16-bit fields in blobs of 256 fields (about 100 records), `C i` = blob `i`.

Records.
* `0 j`   branch on the uncovered time `j`; the children are exactly the allowed coverers of `j`, increasing;
          the child subtrees follow in this order.
* `2 j`   `j` uncovered and no allowed coverer (this includes the case `r = 0`).
* `3 t n v_1 .. v_n`  bound leaf: every allowed class outside `T = {v_i}` covers at most `t` uncovered times,
          every `v_i` at least `t`, and `∑_T cnt + (r - n) t < |unc|`  (r = remaining picks).
* `5 i`   all times covered; the next-level tree `i` must have the descriptor `nx i = (icm, ict, fr)` of this leaf.
* `7 i`   delegated subtree: the state must equal `H i` (the subtree is a separate `checkTask` theorem).
-/

namespace LRSpectrumFull.NineProbe

structure Ctx where
  lvl : Nat
  W : Nat
  full : Nat
  adm : Nat
  m3 : Nat
  ones : Nat
  lowp : Nat
  lowT : Nat
  row : Nat → Nat × Nat × Nat × Nat
  cbJ : Nat → Nat
  cntF : Nat → Nat → Nat

/-- node state. `unc` compact; all others spread except counters. -/
structure St where
  unc : Nat
  cu : Nat
  nu : Nat
  av : Nat
  fr : Nat
  r : Nat
  c3 : Nat
  ch : Nat
  im : Nat
  it : Nat
  mp : Nat
  mq : Nat
  mf : Nat

def ltN (a b : Nat) : Bool := Nat.ble (Nat.add a (nat_lit 1)) b
def rd (C : Nat → Nat) (pos : Nat) : Nat :=
  Nat.land (Nat.shiftRight (C (Nat.shiftRight pos (nat_lit 8))) (Nat.mul (nat_lit 16) (Nat.land pos (nat_lit 255)))) (nat_lit 65535)
def fld (x v : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) v)) (nat_lit 65535)
def bitC (x j : Nat) : Bool := !Nat.beq (Nat.land (Nat.shiftRight x j) (nat_lit 1)) (nat_lit 0)
def nz (x : Nat) : Bool := !Nat.beq x (nat_lit 0)
def clr (x m : Nat) : Nat := Nat.xor x (Nat.land x m)
def sbit (v : Nat) : Nat := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) v)
def lowB (x : Nat) : Nat := Nat.xor x (Nat.land x (Nat.sub x (nat_lit 1)))
def spc (X : Ctx) (x : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul x X.ones) (Nat.mul (nat_lit 16) X.W)) (nat_lit 65535)

def pcl : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, u, acc => bif Nat.beq u (nat_lit 0) then acc else pcl f (Nat.land u (Nat.sub u (nat_lit 1))) (Nat.succ acc)

/-- every field of `L` selected by the spread mask `M` is at most `t` -/
def allLe (X : Ctx) (L M t : Nat) : Bool :=
  ltN t (nat_lit 32768) &&
  Nat.beq (Nat.land (Nat.add L (Nat.mul (Nat.sub (nat_lit 32767) t) X.ones)) (Nat.shiftLeft M (nat_lit 15))) (nat_lit 0)

def readT (C : Nat → Nat) (L t : Nat) : Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | 0, _, s, M, pos => some (s, M, pos)
  | n + 1, pv, s, M, pos =>
    let v := rd C pos
    let lv := fld L v
    bif ltN pv v && Nat.ble t lv then readT C L t n v (Nat.add s lv) (clr M (sbit v)) (Nat.succ pos)
    else none

/-- the `t n T` tail of a bound leaf on loads `L` against `B`, over the allowed mask `av` with `r` picks -/
def tailOK (X : Ctx) (C : Nat → Nat) (L B av r pos : Nat) : Option Nat :=
  let t := rd C pos
  let n := rd C (Nat.succ pos)
  bif Nat.ble n r then
    match readT C L t n (nat_lit 0) (nat_lit 0) av (Nat.add pos (nat_lit 2)) with
    | none => none
    | some (s, M, pos') =>
      bif allLe X L M t && ltN (Nat.add s (Nat.mul (Nat.sub r n) t)) B then some pos' else none
  else none

/-- allowed classes: free picks from `av` (minus multiples of 3 once 6 are chosen), non-forced item lifts, forced item lifts -/
def allowed (X : Ctx) (s : St) : Nat :=
  let F := bif ltN (nat_lit 5) s.c3 then X.m3 else nat_lit 0
  let A0 := Nat.lor (bif Nat.beq s.fr (nat_lit 0) then nat_lit 0 else s.av) (Nat.land (Nat.lor s.mp s.mq) s.av)
  Nat.lor (clr A0 F) (Nat.land s.mf s.av)

/-- the state after taking the class with isolated spread bit `b`; `avr` = available classes for the child -/
def childSt (X : Ctx) (s : St) (b avr : Nat) : St :=
  match X.row b with
  | (c, cc, pc, tc) =>
    let newly := Nat.land s.unc cc
    let inP := nz (Nat.land b s.mp)
    let inQ := nz (Nat.land b s.mq)
    let inF := nz (Nat.land b s.mf)
    { unc := Nat.xor s.unc newly,
      cu := Nat.sub s.cu (X.cntF newly (nat_lit 0)),
      nu := Nat.sub s.nu (fld s.cu c),
      av := avr,
      fr := bif inP || inQ || inF then s.fr else Nat.sub s.fr (nat_lit 1),
      r := Nat.sub s.r (nat_lit 1),
      c3 := Nat.sub (Nat.add s.c3 (bif nz (Nat.land b X.m3) then nat_lit 1 else nat_lit 0)) (bif inF then nat_lit 1 else nat_lit 0),
      ch := Nat.lor s.ch b,
      im := bif inP then clr s.im (Nat.land pc X.lowp) else s.im,
      it := bif inQ || inF then clr s.it (Nat.land tc X.lowT) else s.it,
      mp := bif inP then clr s.mp pc else s.mp,
      mq := bif inQ then clr s.mq tc else s.mq,
      mf := bif inF then clr s.mf tc else s.mf }

/-- the child subtrees of a branch node; `m` = coverers still to do, `avr` = available minus the coverers done -/
def kids (X : Ctx) (g : St → Nat → Option Nat) (s : St) : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | f + 1, m, avr, pos =>
    bif Nat.beq m (nat_lit 0) then some pos else
    let b := lowB m
    let avr' := clr avr b
    match g (childSt X s b avr') pos with
    | none => none
    | some pos' => kids X g s f (clr m b) avr' pos'

/-- descriptor of the next-level tree entered at a leaf -/
def leafOK (X : Ctx) (nx : Nat → Nat × Nat × Nat) (s : St) (i : Nat) : Bool :=
  match nx i with
  | (a, b, c) =>
    Nat.beq s.unc (nat_lit 0) && ltN X.lvl (nat_lit 2) &&
    Nat.beq a (bif Nat.beq X.lvl (nat_lit 0) then s.ch else s.im) &&
    Nat.beq b (bif Nat.beq X.lvl (nat_lit 0) then nat_lit 0 else s.ch) && Nat.beq c s.fr

/-- equality of the node states that are carried (counters are recomputed) -/
def stEq (a b : St) : Bool :=
  Nat.beq a.unc b.unc && Nat.beq a.av b.av && Nat.beq a.fr b.fr && Nat.beq a.r b.r && Nat.beq a.c3 b.c3 &&
  Nat.beq a.ch b.ch && Nat.beq a.im b.im && Nat.beq a.it b.it && Nat.beq a.mp b.mp && Nat.beq a.mq b.mq && Nat.beq a.mf b.mf

/-- replay one subtree -/
def go (X : Ctx) (C : Nat → Nat) (H : Nat → St) (nx : Nat → Nat × Nat × Nat) : Nat → St → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, s, pos =>
    let tag := rd C pos
    bif Nat.beq tag (nat_lit 5) then
      bif leafOK X nx s (rd C (Nat.succ pos)) then some (Nat.add pos (nat_lit 2)) else none
    else bif Nat.beq tag (nat_lit 7) then
      bif stEq (H (rd C (Nat.succ pos))) s then some (Nat.add pos (nat_lit 2)) else none
    else
      let A := allowed X s
      bif Nat.beq tag (nat_lit 0) then
        let j := rd C (Nat.succ pos)
        bif bitC s.unc j then
          kids X (go X C H nx f) s (nat_lit 1024) (Nat.land (X.cbJ j) A) s.av (Nat.add pos (nat_lit 2))
        else none
      else bif Nat.beq tag (nat_lit 2) then
        let j := rd C (Nat.succ pos)
        bif bitC s.unc j && Nat.beq (Nat.land (X.cbJ j) A) (nat_lit 0) then some (Nat.add pos (nat_lit 2)) else none
      else bif Nat.beq tag (nat_lit 3) then tailOK X C s.cu s.nu A s.r (Nat.succ pos)
      else none

def noH : Nat → St := fun _ =>
  { unc := nat_lit 0, cu := nat_lit 0, nu := nat_lit 0, av := nat_lit 0, fr := nat_lit 0, r := nat_lit 99, c3 := nat_lit 0,
    ch := nat_lit 0, im := nat_lit 0, it := nat_lit 0, mp := nat_lit 0, mq := nat_lit 0, mf := nat_lit 0 }

/-- union of `sel (row b)` over the set bits `b` of `u` (at most 16 of them) -/
def orRows (X : Ctx) (sel : Nat × Nat × Nat × Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, u, acc => bif Nat.beq u (nat_lit 0) then acc else
      let b := lowB u
      orRows X sel f (clr u b) (Nat.lor acc (sel (X.row b)))

/-- root state of a tree at level `lvl >= 1` from its descriptor `(icm, ict, fr)` -/
def rootSt (X : Ctx) (icm ict fr : Nat) : St :=
  let ictF := Nat.land ict X.m3
  let ictN := clr ict X.m3
  { unc := X.full, cu := X.cntF X.full (nat_lit 0), nu := X.W, av := X.adm, fr := fr, r := nat_lit 8, c3 := spc X ictF, ch := nat_lit 0,
    im := icm, it := ict,
    mp := orRows X (fun t => t.2.2.1) (nat_lit 16) icm (nat_lit 0),
    mq := orRows X (fun t => t.2.2.2) (nat_lit 16) ictN (nat_lit 0),
    mf := orRows X (fun t => t.2.2.2) (nat_lit 16) ictF (nat_lit 0) }

/-- root state of the level-0 tree: class 1 chosen, 7 picks left -/
def root0 (X : Ctx) : St :=
  let unc := clr X.full (X.row (sbit (nat_lit 1))).2.1
  { unc := unc, cu := X.cntF unc (nat_lit 0), nu := pcl (nat_lit 1024) unc (nat_lit 0), av := clr X.adm (sbit (nat_lit 1)),
    fr := nat_lit 7, r := nat_lit 7, c3 := nat_lit 0, ch := sbit (nat_lit 1), im := nat_lit 0, it := nat_lit 0,
    mp := nat_lit 0, mq := nat_lit 0, mf := nat_lit 0 }

def isSome {α : Type} : Option α → Bool
  | some _ => true
  | none => false

/-- the level-0 tree with delegated subtrees -/
def checkTree0 (X : Ctx) (C : Nat → Nat) (H : Nat → St) (nx : Nat → Nat × Nat × Nat) : Bool :=
  isSome (go X C H nx (nat_lit 12) (root0 X) (nat_lit 0))

/-- one delegated subtree from an explicit state (counters recomputed from `unc`) -/
def checkTask (X : Ctx) (C : Nat → Nat) (nx : Nat → Nat × Nat × Nat) (h : St) : Bool :=
  isSome (go X C noH nx (nat_lit 12)
    { h with cu := X.cntF h.unc (nat_lit 0), nu := pcl (nat_lit 1024) h.unc (nat_lit 0) } (nat_lit 0))

/-- a tree at level `lvl >= 1` from its descriptor; infeasible roots (more than 6 forced multiples of 3) need no certificate -/
def checkRootN (X : Ctx) (C : Nat → Nat) (nx : Nat → Nat × Nat × Nat) (d : Nat × Nat × Nat) : Bool :=
  match d with
  | (icm, ict, fr) =>
    Nat.beq (Nat.add (Nat.add (spc X icm) (spc X ict)) fr) (nat_lit 8) &&
    (bif ltN (nat_lit 6) (spc X (Nat.land ict X.m3)) then true
     else isSome (go X C noH nx (nat_lit 12) (rootSt X icm ict fr) (nat_lit 0)))

end LRSpectrumFull.NineProbe
