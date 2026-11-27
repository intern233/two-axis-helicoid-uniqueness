import TwoAxisHelicoid.TraceDataMiddleParameters013
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters013 : RangeDerivativeParameters := TraceData.middleDerivativeParameters013.interpret
theorem middleDerivativeParameters013_valid : middleDerivativeParameters013.Valid middleRangeSetup (863/1000) (108/125) (325631202149053/549755813888000) (326168073061053/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters013_valid
