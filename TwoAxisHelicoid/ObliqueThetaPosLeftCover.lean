import TwoAxisHelicoid.ObliqueThetaPosLeftGroup000
import TwoAxisHelicoid.ObliqueThetaPosLeftGroup001
namespace TwoAxisHelicoid
theorem obliqueThetaPosLeftCover : CheckedObliqueEdge true false true (1/2) (23/256) (7/16) :=
  (.join checkedObliqueThetaPosLeftGroup000 checkedObliqueThetaPosLeftGroup001)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaPosLeftCover
