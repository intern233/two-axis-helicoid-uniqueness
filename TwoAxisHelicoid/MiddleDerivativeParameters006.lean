import TwoAxisHelicoid.TraceDataMiddleParameters006
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters006 : RangeDerivativeParameters := TraceData.middleDerivativeParameters006.interpret
theorem middleDerivativeParameters006_valid : middleDerivativeParameters006.Valid middleRangeSetup (107/125) (857/1000) (973210252482103/1649267441664000) (974820865218103/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters006_valid
