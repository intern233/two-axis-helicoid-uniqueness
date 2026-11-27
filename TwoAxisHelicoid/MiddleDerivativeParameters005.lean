import TwoAxisHelicoid.TraceDataMiddleParameters005
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters005 : RangeDerivativeParameters := TraceData.middleDerivativeParameters005.interpret
theorem middleDerivativeParameters005_valid : middleDerivativeParameters005.Valid middleRangeSetup (171/200) (107/125) (972687950715697/1649267441664000) (974298563451697/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters005_valid
