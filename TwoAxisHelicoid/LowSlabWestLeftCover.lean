import TwoAxisHelicoid.LowSlabWestLeftGroup000
import TwoAxisHelicoid.LowSlabWestLeftGroup001
namespace TwoAxisHelicoid
theorem lowSlabWestLeftCover : CheckedLowSlabEdge .sector true (0/1) (0/1) (7/16) :=
  (.join checkedLowSlabWestLeftGroup000 checkedLowSlabWestLeftGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabWestLeftCover
