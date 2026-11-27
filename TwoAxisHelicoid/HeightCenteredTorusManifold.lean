import TwoAxisHelicoid.HarmonicTorusManifold
import TwoAxisHelicoid.AxisNormalizationSmooth
import TwoAxisHelicoid.HarmonicIntegerTorusGeometry

namespace TwoAxisHelicoid
open Complex Set
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

theorem heightCenteredTorusPrimitive_contMDiffAt
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {α : ℝ} (hα : α ≠ 0) (b : ℝ) {q : PeriodTorus L} (hq : q ≠ 0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞
      (coordinateToTube ∘ heightCenteredTorusPrimitive L α b X hp) q := by
  rw [heightCenteredTorusPrimitive_eq_space_map L hα]
  exact coordinateToTube.contMDiffAt.comp q
    ((axisSpatialNormalization_contDiff hα ![0,0,b]).contMDiff.contMDiffAt.comp q
      ((hX.torus_contMDiffAt hp hq).of_le (by simp)))

theorem heightCenteredTorusPrimitive_mfderiv_injective
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {α : ℝ} (hα : α ≠ 0) (b : ℝ) {q : PeriodTorus L} (hq : q ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates)
      (coordinateToTube ∘ heightCenteredTorusPrimitive L α b X hp) q) := by
  let F := periodTorusLift L X hp
  let D := axisSpatialNormalization hα ![0,0,b]
  have hf : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q :=
    (hX.torus_contMDiffAt hp hq).mdifferentiableAt (by simp)
  have hd : MDifferentiable 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,Fin 3 → ℝ) D :=
    (axisSpatialNormalization_contDiff hα ![0,0,b]).contMDiff.mdifferentiable (by simp)
  have hdf : Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (D ∘ F) q) := by
    rw [mfderiv_comp q (hd _) hf,mfderiv_eq_fderiv]
    exact (axisSpatialNormalization_fderiv_injective hα ![0,0,b] _).comp
      (hX.torus_mfderiv_injective hp hq)
  rw [heightCenteredTorusPrimitive_eq_space_map L hα]
  change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates)
    (coordinateToTube ∘ (D ∘ F)) q)
  rw [mfderiv_comp q coordinateToTube.mdifferentiableAt
    ((hd _).comp q hf),ContinuousLinearMap.mfderiv_eq]
  exact coordinateToTube_injective.comp hdf

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.heightCenteredTorusPrimitive_contMDiffAt
#print axioms TwoAxisHelicoid.heightCenteredTorusPrimitive_mfderiv_injective
