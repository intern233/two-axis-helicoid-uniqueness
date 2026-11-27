import TwoAxisHelicoid.TraceDataMiddleParameters035
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters035 : RangeDerivativeParameters := TraceData.middleDerivativeParameters035.interpret
theorem middleDerivativeParameters035_valid : middleDerivativeParameters035.Valid middleRangeSetup (177/200) (443/500) (988782639059731/1649267441664000) (990393251795731/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters035_valid
