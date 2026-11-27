import TwoAxisHelicoid.LowSlabMiddleRightGroup000
import TwoAxisHelicoid.LowSlabMiddleRightGroup001
namespace TwoAxisHelicoid
theorem lowSlabMiddleRightCover : CheckedLowSlabEdge .sector true (11/16) (7/32) (7/16) :=
  (.join checkedLowSlabMiddleRightGroup000 checkedLowSlabMiddleRightGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabMiddleRightCover
