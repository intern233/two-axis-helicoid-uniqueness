import TwoAxisHelicoid.TraceDataMiddleParameters029
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters029 : RangeDerivativeParameters := TraceData.middleDerivativeParameters029.interpret
theorem middleDerivativeParameters029_valid : middleDerivativeParameters029.Valid middleRangeSetup (879/1000) (22/25) (985492815320563/1649267441664000) (987103428056563/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters029_valid
