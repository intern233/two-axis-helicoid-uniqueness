import TwoAxisHelicoid.ObliqueThetaNegLeftGroup000
import TwoAxisHelicoid.ObliqueThetaNegLeftGroup001
namespace TwoAxisHelicoid
theorem obliqueThetaNegLeftCover : CheckedObliqueEdge false false true (0/1) (0/1) (7/16) :=
  (.join checkedObliqueThetaNegLeftGroup000 checkedObliqueThetaNegLeftGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaNegLeftCover
