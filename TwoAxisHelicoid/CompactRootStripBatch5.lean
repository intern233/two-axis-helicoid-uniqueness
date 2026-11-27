import TwoAxisHelicoid.CompactRootStripParameters
import TwoAxisHelicoid.CompactRootStripSampling

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactEdge20Up : let b := primalStripOutput compactRootT compactRootP (-3/8) (-11/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge20Down : let b := primalStripOutput compactRootT compactRootP (-3/8) (-11/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge20 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-3/8) (-11/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge20Down
  · exact compactEdge20Up
theorem compactEdge21Up : let b := primalStripOutput compactRootT compactRootP (-11/32) (-5/16) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge21Down : let b := primalStripOutput compactRootT compactRootP (-11/32) (-5/16) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge21 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-11/32) (-5/16) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge21Down
  · exact compactEdge21Up
theorem compactEdge22Up : let b := primalStripOutput compactRootT compactRootP (-5/16) (-9/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge22Down : let b := primalStripOutput compactRootT compactRootP (-5/16) (-9/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge22 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-5/16) (-9/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge22Down
  · exact compactEdge22Up
theorem compactEdge23Up : let b := primalStripOutput compactRootT compactRootP (-9/32) (-1/4) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge23Down : let b := primalStripOutput compactRootT compactRootP (-9/32) (-1/4) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge23 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-9/32) (-1/4) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge23Down
  · exact compactEdge23Up
theorem compactRootStripBatch5 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-3/8) (-1/4) t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactEdge20 tl tu al au) (compactEdge21 tl tu al au)) (CompactRootStripPiece.merge (compactEdge22 tl tu al au) (compactEdge23 tl tu al au)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootStripBatch5
