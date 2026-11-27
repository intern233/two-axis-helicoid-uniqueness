import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell000
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell001
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell002
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell003
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell004
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell005
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell006
import TwoAxisHelicoid.TraceDataSpatialMeanEarlyCell007
namespace TwoAxisHelicoid.TraceData
theorem spatialMeanEarlyCover : CheckedSpatialMean false (7/32) (9/16) (1/1) (-2458065/2097152) (-9342639/8388608) :=
  .cast_bounds (.join (.join (.join checkedSpatialMeanEarlyCell000 checkedSpatialMeanEarlyCell001) (.join checkedSpatialMeanEarlyCell002 checkedSpatialMeanEarlyCell003)) (.join (.join checkedSpatialMeanEarlyCell004 checkedSpatialMeanEarlyCell005) (.join checkedSpatialMeanEarlyCell006 checkedSpatialMeanEarlyCell007))) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.spatialMeanEarlyCover
