import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell000
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell001
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell002
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell003
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell004
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell005
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell006
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell007
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell008
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell009
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell010
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell011
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell012
import TwoAxisHelicoid.TraceDataSpatialMeanLowerCell013
namespace TwoAxisHelicoid.TraceData
theorem spatialMeanLowerCover : CheckedSpatialMean false (3/8) (3/5) (1/1) (-22984197/16777216) (-22356879/16777216) :=
  .cast_bounds (.join (.join (.join checkedSpatialMeanLowerCell000 (.join checkedSpatialMeanLowerCell001 checkedSpatialMeanLowerCell002)) (.join (.join checkedSpatialMeanLowerCell003 checkedSpatialMeanLowerCell004) (.join checkedSpatialMeanLowerCell005 checkedSpatialMeanLowerCell006))) (.join (.join checkedSpatialMeanLowerCell007 (.join checkedSpatialMeanLowerCell008 checkedSpatialMeanLowerCell009)) (.join (.join checkedSpatialMeanLowerCell010 checkedSpatialMeanLowerCell011) (.join checkedSpatialMeanLowerCell012 checkedSpatialMeanLowerCell013)))) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.spatialMeanLowerCover
