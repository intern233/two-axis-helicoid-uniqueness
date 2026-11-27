import TwoAxisHelicoid.CentralArcLeftEarlyGroup000
import TwoAxisHelicoid.CentralArcLeftEarlyGroup001
namespace TwoAxisHelicoid
theorem centralArcLeftEarlyCover : CheckedCentralHeightSweep .leftEarly (0/1) (1/8) :=
  (.join checkedCentralArcLeftEarlyGroup000 checkedCentralArcLeftEarlyGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralArcLeftEarlyCover
