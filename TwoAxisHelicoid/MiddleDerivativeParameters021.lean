import TwoAxisHelicoid.TraceDataMiddleParameters021
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters021 : RangeDerivativeParameters := TraceData.middleDerivativeParameters021.interpret
theorem middleDerivativeParameters021_valid : middleDerivativeParameters021.Valid middleRangeSetup (871/1000) (109/125) (327053920769197/549755813888000) (327590791681197/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters021_valid
