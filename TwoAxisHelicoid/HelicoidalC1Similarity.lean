import TwoAxisHelicoid.CertifiedC1HelicoidEnd

namespace TwoAxisHelicoid
open Set

/-- C¹ helicoidal asymptotics up to a fixed Euclidean similarity. The
positive scale and the Euclidean squared-distance identity are explicit. -/
def HasHelicoidalC1End {M : Type*} [TopologicalSpace M] (X : M → Fin 3 → ℝ) : Prop :=
  ∃ S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ), ∃ dilation : ℝ, 0 < dilation ∧
    (∀ v w : Fin 3 → ℝ, (∑ j, (S v j-S w j)^2) = dilation^2*(∑ j, (v j-w j)^2)) ∧
    HasHelicoidC1End (coordinateToTube ∘ S ∘ X)

theorem HasHelicoidalC1End.of_isometry {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2)
    (h : HasHelicoidalC1End (R ∘ X)) : HasHelicoidalC1End X := by
  obtain ⟨S,dilation,hdilation,hS,hgraph⟩ := h
  refine ⟨R.trans S,dilation,hdilation,?_,hgraph⟩
  intro v w
  simp only [Homeomorph.trans_apply]
  rw [hS,hR]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidalC1End.of_isometry
