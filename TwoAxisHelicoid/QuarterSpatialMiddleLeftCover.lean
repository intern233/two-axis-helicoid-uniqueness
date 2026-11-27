import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup000
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup001
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup002
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup003
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup004
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup005
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup006
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup007
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup008
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup009
import TwoAxisHelicoid.QuarterSpatialMiddleLeftGroup010
namespace TwoAxisHelicoid
theorem quarterSpatialMiddleLeftCover : CheckedQuarterSpatialLine false true true (15/32) (3/8) (1/2) (-887/512) (-1/256) (-725767/4194304) (-827/32768) :=
  .cast_bounds (.join (.join (.join checkedQuarterSpatialMiddleLeftGroup000 checkedQuarterSpatialMiddleLeftGroup001) (.join checkedQuarterSpatialMiddleLeftGroup002 (.join checkedQuarterSpatialMiddleLeftGroup003 checkedQuarterSpatialMiddleLeftGroup004))) (.join (.join checkedQuarterSpatialMiddleLeftGroup005 (.join checkedQuarterSpatialMiddleLeftGroup006 checkedQuarterSpatialMiddleLeftGroup007)) (.join checkedQuarterSpatialMiddleLeftGroup008 (.join checkedQuarterSpatialMiddleLeftGroup009 checkedQuarterSpatialMiddleLeftGroup010)))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialMiddleLeftCover
