import TwoAxisHelicoid.LowSlabSpatialLeftGroup000
import TwoAxisHelicoid.LowSlabSpatialLeftGroup001
import TwoAxisHelicoid.LowSlabSpatialLeftGroup002
import TwoAxisHelicoid.LowSlabSpatialLeftGroup003
import TwoAxisHelicoid.LowSlabSpatialLeftGroup004
namespace TwoAxisHelicoid
theorem lowSlabSpatialLeftCover : CheckedLowSlabEdge (.height false (0/1)) true (15/32) (3/8) (1/2) :=
  (.join (.join checkedLowSlabSpatialLeftGroup000 checkedLowSlabSpatialLeftGroup001) (.join checkedLowSlabSpatialLeftGroup002 (.join checkedLowSlabSpatialLeftGroup003 checkedLowSlabSpatialLeftGroup004)))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabSpatialLeftCover
