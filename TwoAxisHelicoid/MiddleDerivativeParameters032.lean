import TwoAxisHelicoid.TraceDataMiddleParameters032
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters032 : RangeDerivativeParameters := TraceData.middleDerivativeParameters032.interpret
theorem middleDerivativeParameters032_valid : middleDerivativeParameters032.Valid middleRangeSetup (441/500) (883/1000) (987133262649019/1649267441664000) (988743875385019/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters032_valid
