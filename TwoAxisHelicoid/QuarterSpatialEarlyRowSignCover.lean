import TwoAxisHelicoid.QuarterSpatialEarlyRowSignGroup000
import TwoAxisHelicoid.QuarterSpatialEarlyRowSignGroup001
import TwoAxisHelicoid.QuarterSpatialEarlyRowSignGroup002
import TwoAxisHelicoid.QuarterSpatialEarlyRowSignGroup003
import TwoAxisHelicoid.QuarterSpatialEarlyRowSignGroup004
namespace TwoAxisHelicoid
theorem quarterSpatialEarlyRowSignCover : CheckedQuarterSpatialLine false false false (7/32) (9/16) (1/1) (-23645/4096) (-21/2048) (-8213303/4194304) (-1373519/4194304) :=
  .cast_bounds (.join (.join checkedQuarterSpatialEarlyRowSignGroup000 checkedQuarterSpatialEarlyRowSignGroup001) (.join checkedQuarterSpatialEarlyRowSignGroup002 (.join checkedQuarterSpatialEarlyRowSignGroup003 checkedQuarterSpatialEarlyRowSignGroup004))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialEarlyRowSignCover
