import TwoAxisHelicoid.LowSlabWestRightGroup000
import TwoAxisHelicoid.LowSlabWestRightGroup001
namespace TwoAxisHelicoid
theorem lowSlabWestRightCover : CheckedLowSlabEdge .sector true (1/2) (0/1) (7/16) :=
  (.join checkedLowSlabWestRightGroup000 checkedLowSlabWestRightGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabWestRightCover
