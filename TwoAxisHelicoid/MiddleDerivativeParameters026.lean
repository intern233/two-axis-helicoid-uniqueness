import TwoAxisHelicoid.TraceDataMiddleParameters026
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters026 : RangeDerivativeParameters := TraceData.middleDerivativeParameters026.interpret
theorem middleDerivativeParameters026_valid : middleDerivativeParameters026.Valid middleRangeSetup (219/250) (877/1000) (983861273098381/1649267441664000) (985471885834381/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters026_valid
