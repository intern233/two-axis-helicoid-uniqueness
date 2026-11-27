import TwoAxisHelicoid.TraceDataMiddleParameters008
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters008 : RangeDerivativeParameters := TraceData.middleDerivativeParameters008.interpret
theorem middleDerivativeParameters008_valid : middleDerivativeParameters008.Valid middleRangeSetup (429/500) (859/1000) (324752590410507/549755813888000) (325289461322507/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters008_valid
