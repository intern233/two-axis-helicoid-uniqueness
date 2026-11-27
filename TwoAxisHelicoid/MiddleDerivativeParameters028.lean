import TwoAxisHelicoid.TraceDataMiddleParameters028
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters028 : RangeDerivativeParameters := TraceData.middleDerivativeParameters028.interpret
theorem middleDerivativeParameters028_valid : middleDerivativeParameters028.Valid middleRangeSetup (439/500) (879/1000) (984947979621833/1649267441664000) (986558592357833/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters028_valid
