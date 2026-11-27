import TwoAxisHelicoid.CompactRootStripParameters
import TwoAxisHelicoid.CompactRootStripSampling

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactEdge4Up : let b := primalStripOutput compactRootT compactRootP (-7/8) (-27/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge4Down : let b := primalStripOutput compactRootT compactRootP (-7/8) (-27/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge4 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-7/8) (-27/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge4Down
  · exact compactEdge4Up
theorem compactEdge5Up : let b := primalStripOutput compactRootT compactRootP (-27/32) (-13/16) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge5Down : let b := primalStripOutput compactRootT compactRootP (-27/32) (-13/16) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge5 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-27/32) (-13/16) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge5Down
  · exact compactEdge5Up
theorem compactEdge6Up : let b := primalStripOutput compactRootT compactRootP (-13/16) (-25/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge6Down : let b := primalStripOutput compactRootT compactRootP (-13/16) (-25/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge6 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-13/16) (-25/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge6Down
  · exact compactEdge6Up
theorem compactEdge7Up : let b := primalStripOutput compactRootT compactRootP (-25/32) (-3/4) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge7Down : let b := primalStripOutput compactRootT compactRootP (-25/32) (-3/4) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge7 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-25/32) (-3/4) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge7Down
  · exact compactEdge7Up
theorem compactRootStripBatch1 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-7/8) (-3/4) t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactEdge4 tl tu al au) (compactEdge5 tl tu al au)) (CompactRootStripPiece.merge (compactEdge6 tl tu al au) (compactEdge7 tl tu al au)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootStripBatch1
