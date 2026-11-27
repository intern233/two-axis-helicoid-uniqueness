import TwoAxisHelicoid.PdfComplexGrid

namespace TwoAxisHelicoid.PdfVertical

def Grid.point (n : Int) : Grid := ⟨n,n,true⟩
def Grid.mag (a : Grid) : Int := max (-a.lo) a.hi
def CGrid.mag (a : CGrid) : Int := a.re.mag+a.im.mag
def CGrid.guard (a : CGrid) (flag : Bool) : CGrid :=
  ⟨⟨a.re.lo,a.re.hi,a.re.ok && flag⟩,⟨a.im.lo,a.im.hi,a.im.ok && flag⟩⟩

/-- The input seed represents Q*x. Both recurrences share the same
sequence of arguments, beginning at the exponent one. -/
def chordFinite (log : Bool) (q : Grid) (seed : CGrid) : Nat → CGrid × CGrid
  | 0 => (if log then .ofInt 0 else .ofInt 1,seed)
  | n+1 =>
    let (v,p) := chordFinite log q seed n
    let f := (CGrid.ofInt 1).sub p
    (if log then v.add (p.neg.div f) else v.mul f,p.scale q)

def chordEulerProduct (log : Bool) (q : Grid) (seed : CGrid) : CGrid :=
  let (v,p) := chordFinite log q seed 10
  let one := Grid.ofInt 1
  let s := Grid.point q.mag
  let tau := Grid.point p.mag
  let den := one.sub s
  let err := if log then tau.divPos (den.mul (one.sub tau)) else
    (((Grid.ofInt 2).mul (Grid.point v.mag)).mul tau).divPos den
  let flag := q.ok && seed.ok && p.ok && v.ok && err.ok &&
    decide (q.mag<Grid.denom ∧ p.mag+q.mag≤Grid.denom ∧ p.mag<Grid.denom) &&
    (!log || decide (seed.mag<Grid.denom))
  (v.widen err.hi).guard flag

structure ChordParams where
  q : Grid
  kappa : Grid
  r : Grid
  beta : Grid
  h : Grid
  k : Grid
  coeff : Grid
  normal : CGrid

def chordParams (t a : Grid) : ChordParams :=
  let one := Grid.ofInt 1
  let two := Grid.ofInt 2
  let piT := Grid.pi.divPos t
  let q0 := (piT.neg.divNat 2).exp
  let q2 := q0.squared
  let q := q2.neg
  let kappa := piT.mul (one.sub a)
  -- Scale the argument to cover even the large negative exponents at t=1/8.
  let r := (((piT.neg.mul a).divNat 2).exp).squared
  let beta := ((kappa.neg.divNat 2).exp).squared
  let h := (two.mul q0).divPos (one.add q2)
  let k := (one.sub q2).divPos (one.add q2)
  let P := chordEulerProduct false q (.real q)
  let Pr := chordEulerProduct false q (.real (q.mul r))
  let Pi := chordEulerProduct false q (.real beta.neg)
  let num := P.mul P
  let dx := (Pr.mul Pi).scale (one.sub r)
  ⟨q,kappa,r,beta,h,k,(piT.neg.divNat 2).mul k,(num.mul num).div (dx.mul dx)⟩

def chordCellValue (par : ChordParams) (s : Grid) : CGrid :=
  let one := Grid.ofInt 1
  let two := Grid.ofInt 2
  let y := par.k.mul s
  let u : CGrid := ⟨par.h,y⟩
  let n := ((par.k.squared.mul (one.sub s)).mul (one.add s)).neg
  let h2 := par.h.squared
  let d := h2.add (y.sub one).squared
  let di := h2.add (y.add one).squared
  let x : CGrid := ⟨n.divPos d,(two.mul par.h).divPos d⟩
  let ix : CGrid := ⟨n.divPos di,(two.mul par.h).neg.divPos di⟩
  let a := x.scale par.q
  let b := ix.scale par.q
  let c := x.scale (par.q.mul par.r)
  let d' := ix.scale par.beta.neg
  let p := (chordEulerProduct false par.q a).mul (chordEulerProduct false par.q b)
  let pr := (chordEulerProduct false par.q c).mul (chordEulerProduct false par.q d')
  let j := (chordEulerProduct true par.q a).sub (chordEulerProduct true par.q b)
  let f := (((CGrid.ofInt 1).sub (x.scale par.r)).mul pr).div p
  let e := ((u.rot.sub (j.scale two)).scale par.kappa).exp
  (((par.normal.mul x).mul (f.mul f)).mul e).scale par.coeff

end TwoAxisHelicoid.PdfVertical

