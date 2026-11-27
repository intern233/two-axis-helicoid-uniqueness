import TwoAxisHelicoid.CertifiedLowHeightMeanPositions

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Spatial comparisons on the two early and two late windows of
the certified low levels. All displacements are anchored on the
actual infinite vertical axis. -/
theorem certified_low_height_window_positions :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let P := fun z : ℂ => X z 0-X 1 0
    let Y := fun z : ℂ => X z 1-X 1 1
    (∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), 0≤P ⟨x,y⟩) ∧
    (∀ x∈Icc (9/16:ℝ) 1, Y ⟨x,7/32⟩≤5/4) ∧
    (∀ x∈Icc (15/32:ℝ) (3/5), ∀ y∈Icc (3/8:ℝ) (1/2), 5/4<Y ⟨x,y⟩) ∧
    ∀ x∈Icc (15/32:ℝ) (3/5), P ⟨x,1/2⟩<0 :=
  certified_low_height_window_positions_by_means

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_height_window_positions
