import TwoAxisHelicoid.TraceDataMiddleParameters023
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters023 : RangeDerivativeParameters := TraceData.middleDerivativeParameters023.interpret
theorem middleDerivativeParameters023_valid : middleDerivativeParameters023.Valid middleRangeSetup (873/1000) (437/500) (327412870907139/549755813888000) (327949741819139/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters023_valid
