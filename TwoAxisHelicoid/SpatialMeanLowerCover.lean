import TwoAxisHelicoid.TraceDataSpatialMeanLowerCover
import TwoAxisHelicoid.TraceDataSpatialMeanBridge
namespace TwoAxisHelicoid
theorem spatialMeanLowerCover : CheckedHorizontalDisplacement false (3/8) (3/5) (1/1) (-22984197/16777216) (-22356879/16777216) :=
  TraceData.spatialMeanLowerCover.toAnalytic
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialMeanLowerCover
