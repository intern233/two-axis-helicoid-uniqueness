import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.FlatTorusCanonicalDifferential

namespace TwoAxisHelicoid

universe u

/-- On a compact Riemann surface homeomorphic to a torus, holomorphic
one-forms have complex dimension one and each nonzero form has order
zero everywhere in the original atlas. -/
theorem genus_one_canonical_divisor_proved : GenusOneCanonicalDivisorFormula.{u} :=
  genus_one_canonical_divisor_of_one_section
    (genus_one_holomorphic_differential_from_annuli annular_riemann_surface_uniformization_proved)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.genus_one_canonical_divisor_proved
