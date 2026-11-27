import TwoAxisHelicoid.TraceDataMiddleParameters030
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters030 : RangeDerivativeParameters := TraceData.middleDerivativeParameters030.interpret
theorem middleDerivativeParameters030_valid : middleDerivativeParameters030.Valid middleRangeSetup (22/25) (881/1000) (328679546822963/549755813888000) (329216417734963/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters030_valid
