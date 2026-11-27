import TwoAxisHelicoid.PdfVerticalGrid

namespace TwoAxisHelicoid.PdfVertical

def Grid.squared (x : Grid) : Grid :=
  let b := x.mul x
  ⟨max b.lo 0,b.hi,b.ok⟩

def Grid.widen (x : Grid) (radius : Int) : Grid :=
  ⟨x.lo-radius,x.hi+radius,x.ok⟩

structure CGrid where
  re : Grid
  im : Grid
  deriving Repr

namespace CGrid

def real (x : Grid) : CGrid := ⟨x,Grid.ofInt 0⟩
def imaginary (y : Grid) : CGrid := ⟨Grid.ofInt 0,y⟩
def ofInt (n : Int) : CGrid := real (Grid.ofInt n)
def add (a b : CGrid) : CGrid := ⟨a.re.add b.re,a.im.add b.im⟩
def neg (a : CGrid) : CGrid := ⟨a.re.neg,a.im.neg⟩
def sub (a b : CGrid) : CGrid := a.add b.neg
def scale (x : Grid) (a : CGrid) : CGrid := ⟨x.mul a.re,x.mul a.im⟩
def rot (a : CGrid) : CGrid := ⟨a.im.neg,a.re⟩
def mul (a b : CGrid) : CGrid :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im),(a.re.mul b.im).add (a.im.mul b.re)⟩
def inv (a : CGrid) : CGrid :=
  let d := a.re.squared.add a.im.squared
  ⟨a.re.divPos d,a.im.neg.divPos d⟩
def div (a b : CGrid) : CGrid := a.mul b.inv
def divNat (a : CGrid) (n : Nat) : CGrid := ⟨a.re.divNat n,a.im.divNat n⟩
def widen (a : CGrid) (r : Int) : CGrid := ⟨a.re.widen r,a.im.widen r⟩
def ok (a : CGrid) : Bool := a.re.ok && a.im.ok

def taylor (z : CGrid) : Nat → CGrid × CGrid
  | 0 => (ofInt 0,ofInt 1)
  | n+1 =>
    let (s,p) := taylor z n
    (s.add p,(p.mul z).divNat (n+1))

def squareN (z : CGrid) : Nat → CGrid
  | 0 => z
  | n+1 => let s := squareN z n; s.mul s

/-- Cosine and sine at a fixed dyadic argument. -/
def trigPoint (a : Int) : CGrid :=
  let x : Grid := ⟨a,a,decide (-64*Grid.denom≤a ∧ a≤64*Grid.denom)⟩
  let v := (taylor ((imaginary x).divNat 256) 16).1
  squareN (v.widen 32) 8

/-- Each trigonometric coordinate is one-Lipschitz on the real line. -/
def trigBox (x : Grid) : CGrid :=
  let m := (x.lo+x.hi)/2
  let r := max (m-x.lo) (x.hi-m)
  let v := (trigPoint m).widen r
  let flag := x.ok && decide (-64*Grid.denom≤m ∧ m≤64*Grid.denom)
  ⟨⟨v.re.lo,v.re.hi,v.re.ok && flag⟩,⟨v.im.lo,v.im.hi,v.im.ok && flag⟩⟩

def exp (a : CGrid) : CGrid :=
  let b := (a.re.divNat 4).exp.squared.squared
  scale b (trigBox a.im)

end CGrid
end TwoAxisHelicoid.PdfVertical
