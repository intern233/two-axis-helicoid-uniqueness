import TwoAxisHelicoid.QuarterSpatialMiddleBottomGroup000
import TwoAxisHelicoid.QuarterSpatialMiddleBottomGroup001
import TwoAxisHelicoid.QuarterSpatialMiddleBottomGroup002
import TwoAxisHelicoid.QuarterSpatialMiddleBottomGroup003
import TwoAxisHelicoid.QuarterSpatialMiddleBottomGroup004
namespace TwoAxisHelicoid
theorem quarterSpatialMiddleBottomCover : CheckedQuarterSpatialLine false false false (3/8) (15/32) (3/5) (-6109/2048) (-9/4096) (-7525413/20971520) (-894999/20971520) :=
  .cast_bounds (.join (.join checkedQuarterSpatialMiddleBottomGroup000 checkedQuarterSpatialMiddleBottomGroup001) (.join checkedQuarterSpatialMiddleBottomGroup002 (.join checkedQuarterSpatialMiddleBottomGroup003 checkedQuarterSpatialMiddleBottomGroup004))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialMiddleBottomCover
