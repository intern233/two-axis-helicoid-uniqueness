import TwoAxisHelicoid.TraceDataMiddleParameters020
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters020 : RangeDerivativeParameters := TraceData.middleDerivativeParameters020.interpret
theorem middleDerivativeParameters020_valid : middleDerivativeParameters020.Valid middleRangeSetup (87/100) (871/1000) (980624811595613/1649267441664000) (982235424331613/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters020_valid
