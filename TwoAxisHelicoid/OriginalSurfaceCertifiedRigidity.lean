import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.ArbitraryHorizontalAxisRigidity

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The comparison is asserted on the original surface, including its compact
core. The external uniformization, the exterior height/Gauss coordinate and
the intersection result are each explicit in the statement. -/
theorem original_complex_surface_similarity_to_certified {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (hw : RhombicHelicoidIntersectionPrinciple)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (endChart : GeometricExteriorCoordinate X) (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ r : ℝ, A+r • ![c.re,c.im,0] ∈ range X)
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range X)
    {α : ℝ} (hα : α ≠ 0) (hend : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    ∃ (U : M ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ x,
        certifiedTorusImmersion (U x) = scale • E (coordinateToEuclidean (X x))+b := by
  obtain ⟨L,f,Y,_,_,hf,hy,hr,hhi,_,hh,_,hg⟩ :=
    original_surface_marked_torus_reduction top uniform X hX hchart endChart
  obtain ⟨U,k,E,b,hk,he⟩ := marked_arbitrary_horizontal_line_similarity_to_certified hw L Y hy c hc A
    (hr.symm ▸ hline) (hr.symm ▸ hver) hα (hr.symm ▸ hend) hhi hh hg
  exact ⟨f.trans U,k,E,b,hk,fun x => (he (f x)).trans (by rw [hf])⟩

/-- Pass from the original smooth real immersion and geometric zero mean
curvature to the comparison. BBC is used on the complex structure actually
induced by this immersion. The assumed exterior theorem supplies no marking,
periods, curvature classification, parameter, or uniqueness statement. -/
theorem original_real_surface_similarity_to_certified {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (hw : RhombicHelicoidIntersectionPrinciple)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X)
    (hsm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (ho : PositiveSurfaceAtlas M)
    (hm : ∀ x : M, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0)
    (bbc : ∀ (S : ChartedSpace ℂ M), let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M → (∀ e ∈ atlas ℂ M, HarmonicImmersionChart X e) →
        Nonempty (GeometricExteriorCoordinate X))
    (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ) (hline : ∀ r : ℝ, A+r • ![c.re,c.im,0] ∈ range X)
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range X)
    {α : ℝ} (hα : α ≠ 0) (hend : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    ∃ (U : M ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ x,
        certifiedTorusImmersion (U x) = scale • E (coordinateToEuclidean (X x))+b := by
  obtain ⟨S,hs,hchart⟩ := oriented_minimal_induced_harmonic_atlas hsm hi ho hm
  let := S
  let := hs
  obtain ⟨Aend⟩ := bbc S hs hchart
  exact original_complex_surface_similarity_to_certified top uniform hw X hX hchart Aend c hc A hline hver hα hend

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_real_surface_similarity_to_certified
