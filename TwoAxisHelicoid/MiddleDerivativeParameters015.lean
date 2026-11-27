import TwoAxisHelicoid.TraceDataMiddleParameters015
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters015 : RangeDerivativeParameters := TraceData.middleDerivativeParameters015.interpret
theorem middleDerivativeParameters015_valid : middleDerivativeParameters015.Valid middleRangeSetup (173/200) (433/500) (977954771073013/1649267441664000) (979565383809013/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters015_valid
