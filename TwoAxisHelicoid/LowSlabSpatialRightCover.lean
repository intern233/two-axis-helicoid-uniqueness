import TwoAxisHelicoid.LowSlabSpatialRightGroup000
import TwoAxisHelicoid.LowSlabSpatialRightGroup001
import TwoAxisHelicoid.LowSlabSpatialRightGroup002
namespace TwoAxisHelicoid
theorem lowSlabSpatialRightCover : CheckedLowSlabEdge (.height true (1/4)) true (3/5) (3/8) (1/2) :=
  (.join checkedLowSlabSpatialRightGroup000 (.join checkedLowSlabSpatialRightGroup001 checkedLowSlabSpatialRightGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabSpatialRightCover
