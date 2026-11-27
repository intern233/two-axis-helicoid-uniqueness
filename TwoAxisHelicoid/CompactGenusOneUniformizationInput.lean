import TwoAxisHelicoid.GenusOneUniformizationReduction
import TwoAxisHelicoid.OriginalExteriorTorusReduction

namespace TwoAxisHelicoid
universe u

/-- The exact uniformization argument used by the original surface
reduction follows from the classical noncompact simply connected
uniformization dichotomy. All genus-one-specific steps are internal. -/
theorem genus_one_uniformization_input_of_plane_dichotomy
    (uni : TopologicalPlaneUniformization.{u}) (L : PeriodPair) :
    CompactGenusOneUniformization.{u} L := by
  intro N _ _ _ _ _ ht
  obtain ⟨H⟩ := ht
  exact compact_genus_one_uniformization_of_plane_dichotomy H uni

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.genus_one_uniformization_input_of_plane_dichotomy
