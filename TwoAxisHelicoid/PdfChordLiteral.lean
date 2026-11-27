import TwoAxisHelicoid.PdfChordQuadrature

namespace TwoAxisHelicoid.PdfVertical

deriving instance DecidableEq for CGrid
deriving instance DecidableEq for ChordParams

/-- A midpoint split whose two grid sums have already been reduced. -/
theorem chordSpan_of_halves {p : ChordParams} {n : Nat} {l u : Rat} {x y z : CGrid}
    (left : chordSpan p n l ((l+u)/2)=x) (right : chordSpan p n ((l+u)/2) u=y)
    (sum : x.add y=z) : chordSpan p (n+1) l u=z := by
  change (chordSpan p n l ((l+u)/2)).add (chordSpan p n ((l+u)/2) u)=z
  rw [left,right,sum]

theorem chordTiles_of_cons {p : ChordParams} {l u last : Rat} {n : Nat}
    {rest : List (Rat × Nat)} {x y z : CGrid}
    (part : chordSpan p n l u=x) (tail : chordTiles p last u rest=y)
    (join : (x.add y).guard (decide (l<u))=z) :
    chordTiles p last l ((u,n)::rest)=z := by
  unfold chordTiles
  rw [part,tail,join]

theorem horizontalRectangleCheck_of_output {r : HorizontalRectangle} {tl tu al au : Rat}
    {p : ChordParams} {z : CGrid}
    (parameters : chordParams (Grid.ofRats tl tu) (Grid.ofRats al au)=p)
    (integral : chordTiles p 1 (-1) r.tiles=z)
    (valid : (decide (0<tl ∧ tl≤tu ∧ tu≤7/5 ∧ 0<al ∧ al≤au ∧ au<1) &&
      containedInReported z.re r.reLo r.reHi &&
      (if r.isDual then containedInReported z.im r.imLo r.imHi else decide (r.imLo≤0 ∧ 0≤r.imHi)))=true) :
    horizontalRectangleCheck r tl tu al au=true := by
  subst p
  subst z
  exact valid

theorem horizontalRectanglePieces_split_t {r : HorizontalRectangle} {n m : Nat} {tl tu al au : Rat}
    (left : horizontalRectanglePieces r n m tl ((tl+tu)/2) al au=true)
    (right : horizontalRectanglePieces r n m ((tl+tu)/2) tu al au=true) :
    horizontalRectanglePieces r (n+1) m tl tu al au=true := by
  change (_ && _)=true
  rw [left,right]
  rfl

theorem horizontalRectanglePieces_split_a {r : HorizontalRectangle} {m : Nat} {tl tu al au : Rat}
    (left : horizontalRectanglePieces r 0 m tl tu al ((al+au)/2)=true)
    (right : horizontalRectanglePieces r 0 m tl tu ((al+au)/2) au=true) :
    horizontalRectanglePieces r 0 (m+1) tl tu al au=true := by
  change (horizontalRectanglePieces r 0 m tl tu al ((al+au)/2) &&
    horizontalRectanglePieces r 0 m tl tu ((al+au)/2) au)=true
  rw [left,right]
  rfl

end TwoAxisHelicoid.PdfVertical
