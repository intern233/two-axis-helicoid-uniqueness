import TwoAxisHelicoid.QuarterSpatialMiddleRightGroup000
import TwoAxisHelicoid.QuarterSpatialMiddleRightGroup001
import TwoAxisHelicoid.QuarterSpatialMiddleRightGroup002
import TwoAxisHelicoid.QuarterSpatialMiddleRightGroup003
namespace TwoAxisHelicoid
theorem quarterSpatialMiddleRightCover : CheckedQuarterSpatialLine false true true (3/5) (3/8) (1/2) (4001/4096) (2551/512) (78011/524288) (127619/262144) :=
  .cast_bounds (.join (.join checkedQuarterSpatialMiddleRightGroup000 checkedQuarterSpatialMiddleRightGroup001) (.join checkedQuarterSpatialMiddleRightGroup002 checkedQuarterSpatialMiddleRightGroup003)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialMiddleRightCover
