import TwoAxisHelicoid.TraceDataMiddleParameters018
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters018 : RangeDerivativeParameters := TraceData.middleDerivativeParameters018.interpret
theorem middleDerivativeParameters018_valid : middleDerivativeParameters018.Valid middleRangeSetup (217/250) (869/1000) (979553855139569/1649267441664000) (981164467875569/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters018_valid
