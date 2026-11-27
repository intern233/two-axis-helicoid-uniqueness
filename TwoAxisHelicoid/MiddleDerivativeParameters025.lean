import TwoAxisHelicoid.TraceDataMiddleParameters025
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters025 : RangeDerivativeParameters := TraceData.middleDerivativeParameters025.interpret
theorem middleDerivativeParameters025_valid : middleDerivativeParameters025.Valid middleRangeSetup (7/8) (219/250) (327773133521409/549755813888000) (328310004433409/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters025_valid
