import TwoAxisHelicoid.CompactRootStripBatch0
import TwoAxisHelicoid.CompactRootStripBatch1
import TwoAxisHelicoid.CompactRootStripBatch2
import TwoAxisHelicoid.CompactRootStripBatch3
import TwoAxisHelicoid.CompactRootStripBatch4
import TwoAxisHelicoid.CompactRootStripBatch5
import TwoAxisHelicoid.CompactRootStripBatch6
import TwoAxisHelicoid.CompactRootStripBatch7

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compact_original_root_strip {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : CompactRootStripPiece (-1) 0 t a :=
  (CompactRootStripPiece.merge (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactRootStripBatch0 tl tu al au) (compactRootStripBatch1 tl tu al au)) (CompactRootStripPiece.merge (compactRootStripBatch2 tl tu al au) (compactRootStripBatch3 tl tu al au))) (CompactRootStripPiece.merge (CompactRootStripPiece.merge (compactRootStripBatch4 tl tu al au) (compactRootStripBatch5 tl tu al au)) (CompactRootStripPiece.merge (compactRootStripBatch6 tl tu al au) (compactRootStripBatch7 tl tu al au))))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_original_root_strip
