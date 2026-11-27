import TwoAxisHelicoid.TraceDataMiddleParameters009
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters009 : RangeDerivativeParameters := TraceData.middleDerivativeParameters009.interpret
theorem middleDerivativeParameters009_valid : middleDerivativeParameters009.Valid middleRangeSetup (859/1000) (43/50) (974782989612433/1649267441664000) (976393602348433/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters009_valid
