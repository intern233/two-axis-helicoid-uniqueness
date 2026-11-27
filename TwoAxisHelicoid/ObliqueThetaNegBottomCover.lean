import TwoAxisHelicoid.ObliqueThetaNegBottomGroup000
import TwoAxisHelicoid.ObliqueThetaNegBottomGroup001
namespace TwoAxisHelicoid
theorem obliqueThetaNegBottomCover : CheckedObliqueEdge false false false (0/1) (0/1) (125/256) :=
  (.join checkedObliqueThetaNegBottomGroup000 checkedObliqueThetaNegBottomGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaNegBottomCover
