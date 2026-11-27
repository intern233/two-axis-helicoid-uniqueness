import TwoAxisHelicoid.TraceDataMiddleParameters022
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters022 : RangeDerivativeParameters := TraceData.middleDerivativeParameters022.interpret
theorem middleDerivativeParameters022_valid : middleDerivativeParameters022.Valid middleRangeSetup (109/125) (873/1000) (981699695747263/1649267441664000) (983310308483263/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters022_valid
