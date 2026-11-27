import TwoAxisHelicoid.TraceDataMiddleParameters024
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters024 : RangeDerivativeParameters := TraceData.middleDerivativeParameters024.interpret
theorem middleDerivativeParameters024_valid : middleDerivativeParameters024.Valid middleRangeSetup (437/500) (7/8) (982778514048823/1649267441664000) (984389126784823/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters024_valid
