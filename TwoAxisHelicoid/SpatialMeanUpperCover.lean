import TwoAxisHelicoid.TraceDataSpatialMeanUpperCover
import TwoAxisHelicoid.TraceDataSpatialMeanBridge
namespace TwoAxisHelicoid
theorem spatialMeanUpperCover : CheckedHorizontalDisplacement false (1/2) (15/32) (1/1) (-25599107/16777216) (-23151839/16777216) :=
  TraceData.spatialMeanUpperCover.toAnalytic
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialMeanUpperCover
