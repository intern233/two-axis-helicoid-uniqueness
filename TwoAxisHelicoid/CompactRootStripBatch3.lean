import TwoAxisHelicoid.CompactRootStripParameters
import TwoAxisHelicoid.CompactRootStripSampling

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactEdge12Up : let b := primalStripOutput compactRootT compactRootP (-5/8) (-19/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge12Down : let b := primalStripOutput compactRootT compactRootP (-5/8) (-19/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge12 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-5/8) (-19/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge12Down
  · exact compactEdge12Up
theorem compactEdge13Up : let b := primalStripOutput compactRootT compactRootP (-19/32) (-9/16) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge13Down : let b := primalStripOutput compactRootT compactRootP (-19/32) (-9/16) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge13 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-19/32) (-9/16) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge13Down
  · exact compactEdge13Up
theorem compactEdge14Up : let b := primalStripOutput compactRootT compactRootP (-9/16) (-17/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge14Down : let b := primalStripOutput compactRootT compactRootP (-9/16) (-17/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge14 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-9/16) (-17/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge14Down
  · exact compactEdge14Up
theorem compactEdge15Up : let b := primalStripOutput compactRootT compactRootP (-17/32) (-1/2) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge15Down : let b := primalStripOutput compactRootT compactRootP (-17/32) (-1/2) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge15 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-17/32) (-1/2) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge15Down
  · exact compactEdge15Up
theorem compactRootStripBatch3 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-5/8) (-1/2) t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactEdge12 tl tu al au) (compactEdge13 tl tu al au)) (CompactRootStripPiece.merge (compactEdge14 tl tu al au) (compactEdge15 tl tu al au)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootStripBatch3
