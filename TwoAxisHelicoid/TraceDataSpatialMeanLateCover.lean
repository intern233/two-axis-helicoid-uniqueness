import TwoAxisHelicoid.TraceDataSpatialMeanLateCell000
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell001
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell002
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell003
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell004
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell005
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell006
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell007
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell008
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell009
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell010
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell011
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell012
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell013
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell014
import TwoAxisHelicoid.TraceDataSpatialMeanLateCell015
namespace TwoAxisHelicoid.TraceData
theorem spatialMeanLateCover : CheckedSpatialMean true (1/2) (3/5) (1/1) (1277165/16777216) (1580041/16777216) :=
  .cast_bounds (.join (.join (.join (.join checkedSpatialMeanLateCell000 checkedSpatialMeanLateCell001) (.join checkedSpatialMeanLateCell002 checkedSpatialMeanLateCell003)) (.join (.join checkedSpatialMeanLateCell004 checkedSpatialMeanLateCell005) (.join checkedSpatialMeanLateCell006 checkedSpatialMeanLateCell007))) (.join (.join (.join checkedSpatialMeanLateCell008 checkedSpatialMeanLateCell009) (.join checkedSpatialMeanLateCell010 checkedSpatialMeanLateCell011)) (.join (.join checkedSpatialMeanLateCell012 checkedSpatialMeanLateCell013) (.join checkedSpatialMeanLateCell014 checkedSpatialMeanLateCell015)))) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.spatialMeanLateCover
