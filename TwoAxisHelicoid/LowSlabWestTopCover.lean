import TwoAxisHelicoid.LowSlabWestTopGroup000
import TwoAxisHelicoid.LowSlabWestTopGroup001
import TwoAxisHelicoid.LowSlabWestTopGroup002
namespace TwoAxisHelicoid
theorem lowSlabWestTopCover : CheckedLowSlabEdge .sector false (7/16) (0/1) (1/2) :=
  (.join checkedLowSlabWestTopGroup000 (.join checkedLowSlabWestTopGroup001 checkedLowSlabWestTopGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowSlabWestTopCover
