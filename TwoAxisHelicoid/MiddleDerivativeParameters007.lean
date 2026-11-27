import TwoAxisHelicoid.TraceDataMiddleParameters007
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters007 : RangeDerivativeParameters := TraceData.middleDerivativeParameters007.interpret
theorem middleDerivativeParameters007_valid : middleDerivativeParameters007.Valid middleRangeSetup (857/1000) (429/500) (324577841919019/549755813888000) (325114712831019/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters007_valid
