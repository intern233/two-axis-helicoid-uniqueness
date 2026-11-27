import TwoAxisHelicoid.CentralArcLeftLateGroup000
import TwoAxisHelicoid.CentralArcLeftLateGroup001
namespace TwoAxisHelicoid
theorem centralArcLeftLateCover : CheckedCentralHeightSweep .leftLate (3/8) (7/16) :=
  (.join checkedCentralArcLeftLateGroup000 checkedCentralArcLeftLateGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralArcLeftLateCover
