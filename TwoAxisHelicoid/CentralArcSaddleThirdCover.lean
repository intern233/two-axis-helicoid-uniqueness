import TwoAxisHelicoid.CentralArcSaddleThirdGroup000
import TwoAxisHelicoid.CentralArcSaddleThirdGroup001
namespace TwoAxisHelicoid
theorem centralArcSaddleThirdCover : CheckedCentralHeightSweep .saddleThird (0/1) (1/8) :=
  (.join checkedCentralArcSaddleThirdGroup000 checkedCentralArcSaddleThirdGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralArcSaddleThirdCover
