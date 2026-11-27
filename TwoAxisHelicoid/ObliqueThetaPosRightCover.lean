import TwoAxisHelicoid.ObliqueThetaPosRightGroup000
import TwoAxisHelicoid.ObliqueThetaPosRightGroup001
import TwoAxisHelicoid.ObliqueThetaPosRightGroup002
namespace TwoAxisHelicoid
theorem obliqueThetaPosRightCover : CheckedObliqueEdge true false true (1/1) (23/256) (7/16) :=
  (.join checkedObliqueThetaPosRightGroup000 (.join checkedObliqueThetaPosRightGroup001 checkedObliqueThetaPosRightGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaPosRightCover
