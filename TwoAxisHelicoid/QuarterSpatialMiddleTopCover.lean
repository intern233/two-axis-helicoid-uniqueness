import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup000
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup001
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup002
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup003
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup004
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup005
import TwoAxisHelicoid.QuarterSpatialMiddleTopGroup006
namespace TwoAxisHelicoid
theorem quarterSpatialMiddleTopCover : CheckedQuarterSpatialLine false false false (1/2) (15/32) (3/5) (43/4096) (7021/2048) (1115331/20971520) (15905211/41943040) :=
  .cast_bounds (.join (.join checkedQuarterSpatialMiddleTopGroup000 (.join checkedQuarterSpatialMiddleTopGroup001 checkedQuarterSpatialMiddleTopGroup002)) (.join (.join checkedQuarterSpatialMiddleTopGroup003 checkedQuarterSpatialMiddleTopGroup004) (.join checkedQuarterSpatialMiddleTopGroup005 checkedQuarterSpatialMiddleTopGroup006))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialMiddleTopCover
