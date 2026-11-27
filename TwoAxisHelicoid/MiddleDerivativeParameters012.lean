import TwoAxisHelicoid.TraceDataMiddleParameters012
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters012 : RangeDerivativeParameters := TraceData.middleDerivativeParameters012.interpret
theorem middleDerivativeParameters012_valid : middleDerivativeParameters012.Valid middleRangeSetup (431/500) (863/1000) (195272897858239/329853488332800) (195595020405439/329853488332800) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters012_valid
