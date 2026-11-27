import TwoAxisHelicoid.TraceDataMiddleParameters034
import TwoAxisHelicoid.TraceDataBridge
import TwoAxisHelicoid.MiddleRangeSetup
namespace TwoAxisHelicoid
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def middleDerivativeParameters034 : RangeDerivativeParameters := TraceData.middleDerivativeParameters034.interpret
theorem middleDerivativeParameters034_valid : middleDerivativeParameters034.Valid middleRangeSetup (221/250) (177/200) (988231853291513/1649267441664000) (989842466027513/1649267441664000) := by decide +kernel
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.middleDerivativeParameters034_valid
