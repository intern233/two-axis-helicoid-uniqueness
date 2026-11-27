import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup000
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup001
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup002
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup003
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup004
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup005
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup006
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup007
import TwoAxisHelicoid.QuarterSpatialEarlyTopGroup008
namespace TwoAxisHelicoid
theorem quarterSpatialEarlyTopCover : CheckedQuarterSpatialLine true false false (7/32) (1/2) (1/1) (-1117/256) (-71/4096) (-927233/524288) (-77305/262144) :=
  .cast_bounds (.join (.join (.join checkedQuarterSpatialEarlyTopGroup000 checkedQuarterSpatialEarlyTopGroup001) (.join checkedQuarterSpatialEarlyTopGroup002 checkedQuarterSpatialEarlyTopGroup003)) (.join (.join checkedQuarterSpatialEarlyTopGroup004 checkedQuarterSpatialEarlyTopGroup005) (.join checkedQuarterSpatialEarlyTopGroup006 (.join checkedQuarterSpatialEarlyTopGroup007 checkedQuarterSpatialEarlyTopGroup008)))) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarterSpatialEarlyTopCover
