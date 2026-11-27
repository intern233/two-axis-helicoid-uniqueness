import TwoAxisHelicoid.ObliqueThetaPosHeightLeftGroup000
import TwoAxisHelicoid.ObliqueThetaPosHeightLeftGroup001
import TwoAxisHelicoid.ObliqueThetaPosHeightLeftGroup002
namespace TwoAxisHelicoid
theorem obliqueThetaPosHeightLeftCover : CheckedObliqueEdge true true true (1/2) (0/1) (7/16) :=
  (.join checkedObliqueThetaPosHeightLeftGroup000 (.join checkedObliqueThetaPosHeightLeftGroup001 checkedObliqueThetaPosHeightLeftGroup002))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.obliqueThetaPosHeightLeftCover
