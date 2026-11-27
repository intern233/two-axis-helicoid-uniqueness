import TwoAxisHelicoid.PdfChordInterval
import TwoAxisHelicoid.PdfVerticalBoxCheck

namespace TwoAxisHelicoid.PdfVertical

/-- The real path is partitioned into dyadic subintervals of individual
rational spans. A cell encloses every point in its closed span. -/
def chordSpan (p : ChordParams) : Nat → Rat → Rat → CGrid
  | 0,l,u => (chordCellValue p (Grid.ofRats l u)).scale (Grid.ofRats (u-l) (u-l))
  | n+1,l,u =>
    let m := (l+u)/2
    (chordSpan p n l m).add (chordSpan p n m u)

def chordTiles (p : ChordParams) (last : Rat) : Rat → List (Rat × Nat) → CGrid
  | l,[] => (CGrid.ofInt 0).guard (decide (l=last))
  | l,(u,d)::rest =>
    ((chordSpan p d l u).add (chordTiles p last u rest)).guard (decide (l<u))

structure HorizontalRectangle where
  tLo : Rat
  tHi : Rat
  aLo : Rat
  aHi : Rat
  reLo : Rat
  reHi : Rat
  imLo : Rat
  imHi : Rat
  isDual : Bool
  tiles : List (Rat × Nat)

def horizontalRectangleCheck (r : HorizontalRectangle) (tl tu al au : Rat) : Bool :=
  let q := chordParams (Grid.ofRats tl tu) (Grid.ofRats al au)
  let out := chordTiles q 1 (-1) r.tiles
  decide (0<tl ∧ tl≤tu ∧ tu≤7/5 ∧ 0<al ∧ al≤au ∧ au<1) &&
    containedInReported out.re r.reLo r.reHi &&
    (if r.isDual then containedInReported out.im r.imLo r.imHi else decide (r.imLo≤0 ∧ 0≤r.imHi))

def horizontalRectangleAPieces (r : HorizontalRectangle) (tl tu : Rat) : Nat → Rat → Rat → Bool
  | 0,al,au => horizontalRectangleCheck r tl tu al au
  | m+1,al,au =>
    let mid := (al+au)/2
    horizontalRectangleAPieces r tl tu m al mid && horizontalRectangleAPieces r tl tu m mid au

/-- Bisection in both real parameters permits different dependency
widths from the path quadrature. Every leaf evaluates the full rectangle. -/
def horizontalRectanglePieces (r : HorizontalRectangle) : Nat → Nat → Rat → Rat → Rat → Rat → Bool
  | n+1,m,tl,tu,al,au =>
    let mid := (tl+tu)/2
    horizontalRectanglePieces r n m tl mid al au && horizontalRectanglePieces r n m mid tu al au
  | 0,m,tl,tu,al,au => horizontalRectangleAPieces r tl tu m al au

end TwoAxisHelicoid.PdfVertical

