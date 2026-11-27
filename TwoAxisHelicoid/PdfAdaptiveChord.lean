import TwoAxisHelicoid.PdfChordRecordedProducts

namespace TwoAxisHelicoid.PdfVertical

/-- A finite Jacobi product or logarithmic derivative with a certified tail.
Each rectangle can use the truncation order appropriate to its nome. -/
def truncatedChordProduct (N : Nat) (log : Bool) (q : Grid) (seed : CGrid) : CGrid :=
  productWithRemainder log q seed (chordFinite log q seed N)

def truncatedChordCell (N : Nat) (par : ChordParams) (s : Grid) : CGrid :=
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
  let p := (truncatedChordProduct N false par.q a).mul (truncatedChordProduct N false par.q b)
  let pr := (truncatedChordProduct N false par.q c).mul (truncatedChordProduct N false par.q d')
  let j := (truncatedChordProduct N true par.q a).sub (truncatedChordProduct N true par.q b)
  let f := (((CGrid.ofInt 1).sub (x.scale par.r)).mul pr).div p
  let e := ((u.rot.sub (j.scale two)).scale par.kappa).exp
  (((par.normal.mul x).mul (f.mul f)).mul e).scale par.coeff

/-- Every leaf gives an outward-rounded integral over a rational segment.
Each interior node requires adjacent endpoints and an exact sum. -/
inductive AdaptiveChordPath where
  | edge (l u : Rat) (box : CGrid)
  | join (left right : AdaptiveChordPath) (box : CGrid)

namespace AdaptiveChordPath

def lower : AdaptiveChordPath → Rat
  | .edge l _ _ => l
  | .join left _ _ => left.lower

def upper : AdaptiveChordPath → Rat
  | .edge _ u _ => u
  | .join _ right _ => right.upper

def output : AdaptiveChordPath → CGrid
  | .edge _ _ box | .join _ _ box => box

def checked (N : Nat) (p : ChordParams) : AdaptiveChordPath → Bool
  | .edge l u box => decide (l<u ∧
      (truncatedChordCell N p (Grid.ofRats l u)).scale (Grid.ofRats (u-l) (u-l))=box)
  | .join left right box =>
      left.checked N p && right.checked N p &&
        decide (left.upper=right.lower ∧ left.output.add right.output=box)

theorem checked_join {N : Nat} {p : ChordParams} {left right : AdaptiveChordPath} {box : CGrid}
    (hl : left.checked N p=true) (hr : right.checked N p=true)
    (adj : left.upper=right.lower ∧ left.output.add right.output=box) :
    (join left right box).checked N p=true := by
  simp only [checked,hl,hr,Bool.true_and,decide_eq_true_eq]
  exact adj

end AdaptiveChordPath
end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.AdaptiveChordPath.checked_join
