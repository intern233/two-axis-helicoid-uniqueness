import TwoAxisHelicoid.CompactRootStripParameters
import TwoAxisHelicoid.CompactRootStripSampling

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactEdge0Up : let b := primalStripOutput compactRootT compactRootP (-1) (-31/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge0Down : let b := primalStripOutput compactRootT compactRootP (-1) (-31/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge0 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-1) (-31/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge0Down
  · exact compactEdge0Up
theorem compactEdge1Up : let b := primalStripOutput compactRootT compactRootP (-31/32) (-15/16) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge1Down : let b := primalStripOutput compactRootT compactRootP (-31/32) (-15/16) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge1 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-31/32) (-15/16) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge1Down
  · exact compactEdge1Up
theorem compactEdge2Up : let b := primalStripOutput compactRootT compactRootP (-15/16) (-29/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge2Down : let b := primalStripOutput compactRootT compactRootP (-15/16) (-29/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge2 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-15/16) (-29/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge2Down
  · exact compactEdge2Up
theorem compactEdge3Up : let b := primalStripOutput compactRootT compactRootP (-29/32) (-7/8) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge3Down : let b := primalStripOutput compactRootT compactRootP (-29/32) (-7/8) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge3 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-29/32) (-7/8) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge3Down
  · exact compactEdge3Up
theorem compactRootStripBatch0 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-1) (-7/8) t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactEdge0 tl tu al au) (compactEdge1 tl tu al au)) (CompactRootStripPiece.merge (compactEdge2 tl tu al au) (compactEdge3 tl tu al au)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootStripBatch0
