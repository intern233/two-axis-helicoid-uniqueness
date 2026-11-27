import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCover
import TwoAxisHelicoid.TraceDataSpatialMeanBridge
namespace TwoAxisHelicoid
theorem spatialMeanEarlyCover : CheckedHorizontalDisplacement false (7/32) (9/16) (1/1) (-2458065/2097152) (-9342639/8388608) :=
  TraceData.spatialMeanEarlyCover.toAnalytic
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialMeanEarlyCover
