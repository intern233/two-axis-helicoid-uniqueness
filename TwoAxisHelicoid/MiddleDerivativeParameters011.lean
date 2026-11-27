import TwoAxisHelicoid.TraceDataMiddleParameters011
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters011 : RangeDerivativeParameters := TraceData.middleDerivativeParameters011.interpret
theorem middleDerivativeParameters011_valid : middleDerivativeParameters011.Valid middleRangeSetup (861/1000) (431/500) (325278782640451/549755813888000) (325815653552451/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters011_valid
