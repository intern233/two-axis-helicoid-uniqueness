import TwoAxisHelicoid.TraceDataMiddleParameters033
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters033 : RangeDerivativeParameters := TraceData.middleDerivativeParameters033.interpret
theorem middleDerivativeParameters033_valid : middleDerivativeParameters033.Valid middleRangeSetup (883/1000) (221/250) (987682061462147/1649267441664000) (989292674198147/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters033_valid
