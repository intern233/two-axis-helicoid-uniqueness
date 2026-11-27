import TwoAxisHelicoid.LowSlabMiddleBottomGroup000
import TwoAxisHelicoid.LowSlabMiddleBottomGroup001
namespace TwoAxisHelicoid
theorem lowSlabMiddleBottomCover : CheckedLowSlabEdge .sector false (7/32) (1/2) (11/16) :=
  (.join checkedLowSlabMiddleBottomGroup000 checkedLowSlabMiddleBottomGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabMiddleBottomCover
