import TwoAxisHelicoid.ObliqueThetaPosTopGroup000
import TwoAxisHelicoid.ObliqueThetaPosTopGroup001
import TwoAxisHelicoid.ObliqueThetaPosTopGroup002
namespace TwoAxisHelicoid
theorem obliqueThetaPosTopCover : CheckedObliqueEdge true false false (7/16) (1/2) (1/1) :=
  (.join checkedObliqueThetaPosTopGroup000 (.join checkedObliqueThetaPosTopGroup001 checkedObliqueThetaPosTopGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaPosTopCover
