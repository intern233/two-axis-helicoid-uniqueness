import TwoAxisHelicoid.CompactRootStripParameters
import TwoAxisHelicoid.CompactRootStripSampling

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactEdge16Up : let b := primalStripOutput compactRootT compactRootP (-1/2) (-15/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge16Down : let b := primalStripOutput compactRootT compactRootP (-1/2) (-15/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge16 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-1/2) (-15/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge16Down
  · exact compactEdge16Up
theorem compactEdge17Up : let b := primalStripOutput compactRootT compactRootP (-15/32) (-7/16) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge17Down : let b := primalStripOutput compactRootT compactRootP (-15/32) (-7/16) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge17 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-15/32) (-7/16) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge17Down
  · exact compactEdge17Up
theorem compactEdge18Up : let b := primalStripOutput compactRootT compactRootP (-7/16) (-13/32) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge18Down : let b := primalStripOutput compactRootT compactRootP (-7/16) (-13/32) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge18 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-7/16) (-13/32) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge18Down
  · exact compactEdge18Up
theorem compactEdge19Up : let b := primalStripOutput compactRootT compactRootP (-13/32) (-3/8) (5/16) (5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge19Down : let b := primalStripOutput compactRootT compactRootP (-13/32) (-3/8) (-5/16) (-5/16)
  b.ok=true ∧ b.mag≤10^6*Grid.denom := by decide +kernel
theorem compactEdge19 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-13/32) (-3/8) t a := by
  apply compact_root_strip_piece (T:=compactRootT) (Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)) (compactRootP_sound tl tu al au) (by linarith)
  intro f
  cases f
  · exact compactEdge19Down
  · exact compactEdge19Up
theorem compactRootStripBatch4 {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-1/2) (-3/8) t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactEdge16 tl tu al au) (compactEdge17 tl tu al au)) (CompactRootStripPiece.merge (compactEdge18 tl tu al au) (compactEdge19 tl tu al au)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootStripBatch4
