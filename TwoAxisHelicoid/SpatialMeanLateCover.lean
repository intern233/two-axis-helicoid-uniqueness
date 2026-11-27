import TwoAxisHelicoid.TraceDataSpatialMeanLateCover
import TwoAxisHelicoid.TraceDataSpatialMeanBridge
namespace TwoAxisHelicoid
theorem spatialMeanLateCover : CheckedHorizontalDisplacement true (1/2) (3/5) (1/1) (1277165/16777216) (1580041/16777216) :=
  TraceData.spatialMeanLateCover.toAnalytic
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialMeanLateCover
