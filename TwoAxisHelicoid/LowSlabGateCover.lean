import TwoAxisHelicoid.LowSlabGateGroup000
import TwoAxisHelicoid.LowSlabGateGroup001
import TwoAxisHelicoid.LowSlabGateGroup002
namespace TwoAxisHelicoid
theorem lowSlabGateCover : CheckedLowSlabEdge (.height true (1/4)) true (11/16) (7/32) (7/16) :=
  (.join checkedLowSlabGateGroup000 (.join checkedLowSlabGateGroup001 checkedLowSlabGateGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabGateCover
