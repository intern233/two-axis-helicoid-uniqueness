import TwoAxisHelicoid.TraceDataMiddleParameters019
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters019 : RangeDerivativeParameters := TraceData.middleDerivativeParameters019.interpret
theorem middleDerivativeParameters019_valid : middleDerivativeParameters019.Valid middleRangeSetup (869/1000) (87/100) (326696280934847/549755813888000) (327233151846847/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters019_valid
