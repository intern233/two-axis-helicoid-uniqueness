import TwoAxisHelicoid.TraceDataMiddleParameters003
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters003 : RangeDerivativeParameters := TraceData.middleDerivativeParameters003.interpret
theorem middleDerivativeParameters003_valid : middleDerivativeParameters003.Valid middleRangeSetup (853/1000) (427/500) (971646258964651/1649267441664000) (973256871700651/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters003_valid
