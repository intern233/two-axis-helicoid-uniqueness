import TwoAxisHelicoid.QuarterSpatialEarlyLeftGroup000
import TwoAxisHelicoid.QuarterSpatialEarlyLeftGroup001
import TwoAxisHelicoid.QuarterSpatialEarlyLeftGroup002
namespace TwoAxisHelicoid
theorem quarterSpatialEarlyLeftCover : CheckedQuarterSpatialLine true false true (1/2) (0/1) (7/32) (-79397/4096) (-25/1024) (-1323469/524288) (-1464169/4194304) :=
  .cast_bounds (.join checkedQuarterSpatialEarlyLeftGroup000 (.join checkedQuarterSpatialEarlyLeftGroup001 checkedQuarterSpatialEarlyLeftGroup002)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialEarlyLeftCover
