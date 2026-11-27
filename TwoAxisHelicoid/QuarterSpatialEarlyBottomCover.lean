import TwoAxisHelicoid.QuarterSpatialEarlyBottomGroup000
import TwoAxisHelicoid.QuarterSpatialEarlyBottomGroup001
namespace TwoAxisHelicoid
theorem quarterSpatialEarlyBottomCover : CheckedQuarterSpatialLine true false false (0/1) (1/2) (1/1) (-70057/4096) (-2221/4096) (-251751/65536) (-52605/131072) :=
  .cast_bounds (.join checkedQuarterSpatialEarlyBottomGroup000 checkedQuarterSpatialEarlyBottomGroup001) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialEarlyBottomCover
