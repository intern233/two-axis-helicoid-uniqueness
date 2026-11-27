import TwoAxisHelicoid.TraceDataMiddleParameters016
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters016 : RangeDerivativeParameters := TraceData.middleDerivativeParameters016.interpret
theorem middleDerivativeParameters016_valid : middleDerivativeParameters016.Valid middleRangeSetup (433/500) (867/1000) (326162273349547/549755813888000) (326699144261547/549755813888000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters016_valid
