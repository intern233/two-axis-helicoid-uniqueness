import TwoAxisHelicoid.TraceDataMiddleParameters027
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters027 : RangeDerivativeParameters := TraceData.middleDerivativeParameters027.interpret
theorem middleDerivativeParameters027_valid : middleDerivativeParameters027.Valid middleRangeSetup (877/1000) (439/500) (984404132502007/1649267441664000) (986014745238007/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters027_valid
