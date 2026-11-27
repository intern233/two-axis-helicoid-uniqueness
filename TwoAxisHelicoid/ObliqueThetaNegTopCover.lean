import TwoAxisHelicoid.ObliqueThetaNegTopGroup000
import TwoAxisHelicoid.ObliqueThetaNegTopGroup001
namespace TwoAxisHelicoid
theorem obliqueThetaNegTopCover : CheckedObliqueEdge false false false (7/16) (0/1) (125/256) :=
  (.join checkedObliqueThetaNegTopGroup000 checkedObliqueThetaNegTopGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaNegTopCover
