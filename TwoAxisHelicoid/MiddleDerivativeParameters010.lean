import TwoAxisHelicoid.TraceDataMiddleParameters010
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters010 : RangeDerivativeParameters := TraceData.middleDerivativeParameters010.interpret
theorem middleDerivativeParameters010_valid : middleDerivativeParameters010.Valid middleRangeSetup (43/50) (861/1000) (975309181602737/1649267441664000) (976919794338737/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters010_valid
