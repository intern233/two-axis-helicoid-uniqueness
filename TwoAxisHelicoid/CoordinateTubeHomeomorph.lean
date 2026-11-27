import TwoAxisHelicoid.ControlledCurvesTransfer

namespace TwoAxisHelicoid

noncomputable def coordinateTubeHomeomorph : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates where
  toFun := coordinateToTube
  invFun := tubeCartesian
  left_inv := tubeCartesian_coordinateToTube
  right_inv _ := rfl
  continuous_toFun := coordinateToTube.continuous
  continuous_invFun := by
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [tubeCartesian] <;> fun_prop

@[simp] theorem coordinateTubeHomeomorph_apply (v : Fin 3 → ℝ) :
    coordinateTubeHomeomorph v = coordinateToTube v := rfl

theorem coordinateToTube_isProperMap {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (hX : IsProperMap X) :
    IsProperMap (coordinateToTube ∘ X) :=
  coordinateTubeHomeomorph.isProperMap.comp hX

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateToTube_isProperMap
