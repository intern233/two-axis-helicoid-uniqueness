import TwoAxisHelicoid.HelicoidGraphPositionalAsymptote
import TwoAxisHelicoid.AffineHelicoidAsymptotics

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology

noncomputable def centeredHelicoidNormalization {α : ℝ} (hα : α ≠ 0) :
    (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) where
  toEquiv := (axisSpatialNormalization hα 0).toEquiv
  map_add' := fun x y => by
    change axisSpatialNormalization hα 0 (x+y) = axisSpatialNormalization hα 0 x+axisSpatialNormalization hα 0 y
    simp only [axisSpatialNormalization_apply,map_add,map_zero,sub_zero,smul_add]
  map_smul' := fun t x => by
    change axisSpatialNormalization hα 0 (t • x) = t • axisSpatialNormalization hα 0 x
    simp only [axisSpatialNormalization_apply,map_zero,sub_zero,map_smul]
    rw [smul_comm]
  continuous_toFun := (axisSpatialNormalization hα 0).continuous
  continuous_invFun := (axisSpatialNormalization hα 0).symm.continuous

/-- Decay of the single normal graph over the actual reference helicoid
implies both one-sided distance estimates in the original coordinate frame.
These positional estimates are therefore available when invoking the
geometric nonplanarity and axis-alignment results. -/
theorem reference_graph_positional_asymptote {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) (hX : Continuous X) {α : ℝ} (hα : α ≠ 0)
    (hend : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,0] ∘ X)) :
    ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0)) ∧
    ApproachesSetAtInfinity (range (axisRuledHelicoid I α 0)) (range X) := by
  let R := centeredHelicoidNormalization hα
  have hz : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext j; fin_cases j <;> rfl
  rw [hz] at hend
  have hY : Continuous (coordinateToTube ∘ axisSpatialNormalization hα 0 ∘ X) :=
    coordinateToTube.continuous.comp ((axisSpatialNormalization hα 0).continuous.comp hX)
  have hg := hend.positional_asymptote hY
  have hr : range (tubeCartesian ∘ coordinateToTube ∘ axisSpatialNormalization hα 0 ∘ X) = R '' range X := by
    rw [← range_comp]
    exact congrArg range (funext fun x => tubeCartesian_coordinateToTube _)
  have hstd : range (fun p : ℝ × ℝ => standardHelicoid p.1 p.2) = range (fun z : ℂ => standardHelicoid z.re z.im) := by
    ext v
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨⟨p.1,p.2⟩,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨(z.re,z.im),rfl⟩
  have he : range (fun z : ℂ => standardHelicoid z.re z.im) = R '' range (axisRuledHelicoid I α 0) := by
    have hp := inverse_image_standardHelicoid_axisNormalization hα 0
    rw [hz] at hp
    change R ⁻¹' range (fun z : ℂ => standardHelicoid z.re z.im) = _ at hp
    rw [← hp,image_preimage_eq _ R.surjective]
  change ApproachesSetAtInfinity (range _) (range _) ∧ ApproachesSetAtInfinity (range _) (range _) at hg
  rw [hr,hstd,he] at hg
  have hback (S T : Set (Fin 3 → ℝ)) :
      ApproachesSetAtInfinity (R '' S) (R '' T) ↔ ApproachesSetAtInfinity S T := by
    simpa only [zero_add] using ApproachesSetAtInfinity.affine_equiv S T R 0
  exact ⟨(hback _ _).mp hg.1,(hback _ _).mp hg.2⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.reference_graph_positional_asymptote
