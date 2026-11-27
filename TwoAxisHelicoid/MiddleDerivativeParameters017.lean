import TwoAxisHelicoid.TraceDataMiddleParameters017
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters017 : RangeDerivativeParameters := TraceData.middleDerivativeParameters017.interpret
theorem middleDerivativeParameters017_valid : middleDerivativeParameters017.Valid middleRangeSetup (867/1000) (217/250) (326339949271293/549755813888000) (326876820183293/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters017_valid
