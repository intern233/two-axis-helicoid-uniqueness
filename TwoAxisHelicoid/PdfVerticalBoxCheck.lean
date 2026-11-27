import TwoAxisHelicoid.PdfVerticalGrid

namespace TwoAxisHelicoid.PdfVertical

def pairedBoxTerm (q E e p : Grid) : Grid :=
  let s := p.mul q
  let one := Grid.ofInt 1
  let d := (one.sub (s.mul e)).mul (one.add (s.mul E))
  let top := ((e.sub E).mul (one.sub (s.mul s))).add ((Grid.ofInt 4).mul s)
  (p.mul top).divPos (d.mul d)

def pairedBoxSum (q E e Q : Grid) : Nat → Grid × Grid
  | 0 => (Grid.ofInt 1,Grid.ofInt 0)
  | n+1 =>
    let (p,total) := pairedBoxSum q E e Q n
    (p.mul Q,total.add (pairedBoxTerm q E e p))

def pairedBoxWithTail (q E : Grid) : Grid :=
  let one := Grid.ofInt 1
  let e := one.divPos E
  let Q := (q.mul q).neg
  let (p,total) := pairedBoxSum q E e Q 12
  let tail := (((Grid.ofInt 4).mul (e.add E)).mul p).divPos (one.add Q)
  ⟨total.lo-tail.hi,total.hi+tail.hi,
    total.ok && tail.ok && p.ok && decide (2*p.hi≤Grid.denom)⟩

def verticalValueBox (dual : Bool) (t a : Grid) : Grid :=
  let q := (Grid.pi.neg.divPos ((Grid.ofInt 2).mul t)).exp
  let E := ((Grid.pi.mul (a.sub (Grid.ofRats (1/2) (1/2)))).divPos t).exp
  let total := pairedBoxWithTail q E
  if dual then total else (((Grid.pi.mul Grid.pi).mul q).divPos (t.mul t)).mul total

def containedInReported (out : Grid) (lo hi : Rat) : Bool :=
  out.ok && decide (lo.num*Grid.denom≤out.lo*(lo.den:Int)) &&
    decide (out.hi*(hi.den:Int)≤hi.num*Grid.denom)

def verticalCover (dual : Bool) (endT a lo hi : Rat) (t : Rat) : List Rat → Bool
  | [] => decide (t=endT)
  | u::rest => decide (t<u) &&
    containedInReported (verticalValueBox dual (Grid.ofRats t u) (Grid.ofRats a a)) lo hi &&
    verticalCover dual endT a lo hi u rest

structure VerticalRow where
  tLo : Rat
  tHi : Rat
  aLo : Rat
  aHi : Rat
  vLoLeft : Rat
  vLoRight : Rat
  vHiLeft : Rat
  vHiRight : Rat
  lowerCuts : List Rat
  upperCuts : List Rat

def VerticalRow.dual (r : VerticalRow) : Bool := decide (r.tHi<3/5)
def VerticalRow.verified (r : VerticalRow) : Bool :=
  decide (0<r.tLo ∧ r.tLo<r.tHi ∧ 0<r.aLo ∧ r.aLo<r.aHi ∧ r.aHi<1) &&
  verticalCover r.dual r.tHi r.aLo r.vLoLeft r.vLoRight r.tLo r.lowerCuts &&
  verticalCover r.dual r.tHi r.aHi r.vHiLeft r.vHiRight r.tLo r.upperCuts

end TwoAxisHelicoid.PdfVertical

