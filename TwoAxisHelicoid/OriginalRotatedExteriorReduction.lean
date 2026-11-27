import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.AmbientHarmonicImmersion

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology Manifold ContDiff

universe u

theorem orthogonal_affine_harmonic_charts {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (hR : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b) (P : Fin 3 → ℝ) :
    ∀ d ∈ atlas ℂ M, HarmonicImmersionChart (fun x => P+R (X x)) d := by
  intro d hd z hz
  obtain ⟨hh,hc,hr⟩ := hX d hd z hz
  exact orthogonal_affine_harmonic_immersion R hR P hh hc hr

/-- The BBC end chart may be furnished in a rotated ambient frame.
The two actual positional asymptotics identify its axis with the one
specified for the original surface. The resulting marked torus
parametrizes the original position and has both double poles in that
position. -/
theorem original_rotated_exterior_marked_torus_reduction {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X)
    (R : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (hR : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b) (P : Fin 3 → ℝ)
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h₁ : ApproachesSetAtInfinity ((fun p => P+R p) '' range (axisRuledHelicoid I β 0))
      (range (fun x => P+R (X x))))
    (h₂ : ApproachesSetAtInfinity (range (fun x => P+R (X x))) (range (axisRuledHelicoid I α 0))) :
    let placed := fun x => P+R (X x)
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x).1 = placed x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1) = range placed ∧
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
        Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
      MeromorphicAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 = -2 := by
  obtain ⟨L,f,Z,hf,hi,hfZ,hZ,himage,hhi,hmh,hho,hmg,hgo⟩ :=
    original_surface_marked_torus_reduction top uniform X hX hchart A
  let T := R.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft P)
  let Y := fun q : PeriodTorus L => P+R (Z q)
  let π := periodTorusProjection L
  have hdata := asymptotic_helicoid_actual_end_double_poles R.toLinearMap hR P α β hα hβ h₁ h₂
    (Z ∘ π) 0 (marked_harmonic_end_null hhi) hmh hho hmg hgo
  have hyy : range (fun q : PuncturedPeriodTorus L => Y q.1) = range (fun x => P+R (X x)) := by
    change range (T ∘ (fun q : PuncturedPeriodTorus L => Z q.1)) = range (T ∘ X)
    rw [Set.range_comp,Set.range_comp,himage]
  refine ⟨L,f,Y,hf,hi,fun x => congrArg (fun v => P+R v) (hfZ x),T.isClosedEmbedding.comp hZ,hyy,?_,hdata⟩
  intro z hz
  obtain ⟨hh,hc,hr⟩ := hhi _ hz
  exact orthogonal_affine_harmonic_immersion R hR P hh hc hr

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_rotated_exterior_marked_torus_reduction
