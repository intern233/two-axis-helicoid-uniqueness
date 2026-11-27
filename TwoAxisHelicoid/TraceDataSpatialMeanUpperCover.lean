import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell000
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell001
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell002
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell003
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell004
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell005
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell006
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell007
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell008
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell009
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell010
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell011
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell012
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell013
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell014
import TwoAxisHelicoid.TraceDataSpatialMeanUpperCell015
namespace TwoAxisHelicoid.TraceData
theorem spatialMeanUpperCover : CheckedSpatialMean false (1/2) (15/32) (1/1) (-25599107/16777216) (-23151839/16777216) :=
  .cast_bounds (.join (.join (.join (.join checkedSpatialMeanUpperCell000 checkedSpatialMeanUpperCell001) (.join checkedSpatialMeanUpperCell002 checkedSpatialMeanUpperCell003)) (.join (.join checkedSpatialMeanUpperCell004 checkedSpatialMeanUpperCell005) (.join checkedSpatialMeanUpperCell006 checkedSpatialMeanUpperCell007))) (.join (.join (.join checkedSpatialMeanUpperCell008 checkedSpatialMeanUpperCell009) (.join checkedSpatialMeanUpperCell010 checkedSpatialMeanUpperCell011)) (.join (.join checkedSpatialMeanUpperCell012 checkedSpatialMeanUpperCell013) (.join checkedSpatialMeanUpperCell014 checkedSpatialMeanUpperCell015)))) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.spatialMeanUpperCover
