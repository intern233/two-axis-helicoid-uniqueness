import Init.Data.Rat

namespace TwoAxisHelicoid.PdfVertical

/-- Integer endpoints in units of 2^-80. Every operation propagates the
domain checks for positive division and for the Taylor estimate. -/
structure Grid where
  lo : Int
  hi : Int
  ok : Bool := true
  deriving Repr, DecidableEq

namespace Grid

def denom : Int := 2^80

def ofInt (n : Int) : Grid := ⟨n*denom,n*denom,true⟩

def ofRats (a b : Rat) : Grid :=
  ⟨(a.num*denom)/(a.den:Int),-((-b.num*denom)/(b.den:Int)),true⟩

def add (a b : Grid) : Grid := ⟨a.lo+b.lo,a.hi+b.hi,a.ok && b.ok⟩
def neg (a : Grid) : Grid := ⟨-a.hi,-a.lo,a.ok⟩
def sub (a b : Grid) : Grid := a.add b.neg

def mul (a b : Grid) : Grid :=
  let c := a.lo*b.lo
  let d := a.lo*b.hi
  let e := a.hi*b.lo
  let f := a.hi*b.hi
  ⟨min (min c d) (min e f)/denom,-((-max (max c d) (max e f))/denom),a.ok && b.ok⟩

def invPos (a : Grid) : Grid :=
  ⟨(denom*denom)/a.hi,-((-(denom*denom))/a.lo),a.ok && decide (0<a.lo)⟩

def divPos (a b : Grid) : Grid := a.mul b.invPos

def divNat (a : Grid) (n : Nat) : Grid :=
  ⟨a.lo/(n:Int),-((-a.hi)/(n:Int)),a.ok && decide (n≠0)⟩

def taylor (a : Grid) : Nat → Grid × Grid
  | 0 => (ofInt 0,ofInt 1)
  | n+1 =>
    let (s,v) := taylor a n
    (s.add v,(v.mul a).divNat (n+1))

def squareN (a : Grid) : Nat → Grid
  | 0 => a
  | n+1 => let r := squareN a n; r.mul r

def expPoint (a : Int) : Grid :=
  let x : Grid := ⟨a,a,decide (-16*denom≤a ∧ a≤16*denom)⟩
  let v := (taylor (x.divNat 64) 16).1
  squareN (v.add ⟨-32,32,true⟩) 6

def exp (a : Grid) : Grid :=
  let l := expPoint a.lo
  let h := expPoint a.hi
  ⟨l.lo,h.hi,a.ok && l.ok && h.ok && decide (-16*denom≤a.lo ∧ a.hi≤16*denom)⟩

def pi : Grid := ofRats (314159265358979323846/10^20) (314159265358979323847/10^20)

end Grid
end TwoAxisHelicoid.PdfVertical

