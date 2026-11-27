import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup000
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup001
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup002
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup003
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup004
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup005
import TwoAxisHelicoid.QuarterSpatialLateHorizontalGroup006
namespace TwoAxisHelicoid
theorem quarterSpatialLateHorizontalCover : CheckedQuarterSpatialLine true false false (1/2) (15/32) (3/5) (7/2048) (1149/256) (27363/524288) (15543339/41943040) :=
  .cast_bounds (.join (.join checkedQuarterSpatialLateHorizontalGroup000 (.join checkedQuarterSpatialLateHorizontalGroup001 checkedQuarterSpatialLateHorizontalGroup002)) (.join (.join checkedQuarterSpatialLateHorizontalGroup003 checkedQuarterSpatialLateHorizontalGroup004) (.join checkedQuarterSpatialLateHorizontalGroup005 checkedQuarterSpatialLateHorizontalGroup006))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialLateHorizontalCover
