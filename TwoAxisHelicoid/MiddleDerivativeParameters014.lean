import TwoAxisHelicoid.TraceDataMiddleParameters014
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters014 : RangeDerivativeParameters := TraceData.middleDerivativeParameters014.interpret
theorem middleDerivativeParameters014_valid : middleDerivativeParameters014.Valid middleRangeSetup (108/125) (173/200) (977423700124141/1649267441664000) (979034312860141/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters014_valid
