import TwoAxisHelicoid.PdfChordLiteral

namespace TwoAxisHelicoid.PdfVertical

theorem chordSpan_of_halves_at {p : ChordParams} {n : Nat} {l mid u : Rat} {x y z : CGrid}
    (left : chordSpan p n l mid=x) (right : chordSpan p n mid u=y)
    (sum : x.add y=z) (same : (l+u)/2=mid) : chordSpan p (n+1) l u=z := by
  subst mid
  exact chordSpan_of_halves left right sum

theorem horizontalRectanglePieces_split_t_at {r : HorizontalRectangle} {n m : Nat} {tl mid tu al au : Rat}
    (left : horizontalRectanglePieces r n m tl mid al au=true)
    (right : horizontalRectanglePieces r n m mid tu al au=true)
    (same : (tl+tu)/2=mid) :
    horizontalRectanglePieces r (n+1) m tl tu al au=true := by
  subst mid
  exact horizontalRectanglePieces_split_t left right

theorem horizontalRectanglePieces_split_a_at {r : HorizontalRectangle} {m : Nat} {tl tu al mid au : Rat}
    (left : horizontalRectanglePieces r 0 m tl tu al mid=true)
    (right : horizontalRectanglePieces r 0 m tl tu mid au=true)
    (same : (al+au)/2=mid) :
    horizontalRectanglePieces r 0 (m+1) tl tu al au=true := by
  subst mid
  exact horizontalRectanglePieces_split_a left right

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordSpan_of_halves_at
