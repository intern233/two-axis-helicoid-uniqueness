import TwoAxisHelicoid.TraceDataMiddleParameters031
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters031 : RangeDerivativeParameters := TraceData.middleDerivativeParameters031.interpret
theorem middleDerivativeParameters031_valid : middleDerivativeParameters031.Valid middleRangeSetup (881/1000) (441/500) (197317091189897/329853488332800) (197639213737097/329853488332800) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters031_valid
