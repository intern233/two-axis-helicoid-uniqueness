import TwoAxisHelicoid.TraceDataMiddleParameters004
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters004 : RangeDerivativeParameters := TraceData.middleDerivativeParameters004.interpret
theorem middleDerivativeParameters004_valid : middleDerivativeParameters004.Valid middleRangeSetup (427/500) (171/200) (972166619770871/1649267441664000) (973777232506871/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters004_valid
