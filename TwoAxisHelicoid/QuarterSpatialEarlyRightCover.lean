import TwoAxisHelicoid.QuarterSpatialEarlyRightGroup000
import TwoAxisHelicoid.QuarterSpatialEarlyRightGroup001
namespace TwoAxisHelicoid
theorem quarterSpatialEarlyRightCover : CheckedQuarterSpatialLine true false true (1/1) (0/1) (7/32) (-4983/1024) (-263/2048) (-1907549/2097152) (-22225/131072) :=
  .cast_bounds (.join checkedQuarterSpatialEarlyRightGroup000 checkedQuarterSpatialEarlyRightGroup001) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialEarlyRightCover
