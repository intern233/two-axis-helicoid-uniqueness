import TwoAxisHelicoid.OriginalRotatedExteriorReduction
import TwoAxisHelicoid.AffineHelicoidAsymptotics

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The analytic coordinate and the helicoidal asymptote provided by the
geometric end theorem in its own Euclidean frame. All positions in this
witness are related to the given immersion by the displayed rigid motion. -/
structure GeometricExteriorInSomeFrame {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) where
  frame : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)
  orthogonal : ∀ u v, frame u ⬝ᵥ frame v = u ⬝ᵥ v
  offset : Fin 3 → ℝ
  exterior : GeometricExteriorCoordinate (fun x => offset+frame (X x))
  pitch : ℝ
  nonzero : pitch ≠ 0
  approaching : ApproachesSetAtInfinity (range (axisRuledHelicoid I pitch 0)) (range (fun x => offset+frame (X x)))

/-- Identify the BBC frame with the original asymptotic axis using actual
two-frame placements. The following marked immersion is in the original
coordinates supplied by the problem. -/
theorem original_surface_from_arbitrary_exterior_frame {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (X : M → Fin 3 → ℝ)
    (hX : IsClosedEmbedding X) (hchart : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorInSomeFrame X) {α : ℝ} (hα : α ≠ 0)
    (hend : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ x, Y (f x).1 = X x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1) = range X ∧
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
        Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 = -2 ∧
      meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 = -2 := by
  let Z := fun x => A.offset+A.frame (X x)
  let R := A.frame.symm
  let P := -(R A.offset)
  let T := A.frame.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft A.offset)
  have hZ : IsClosedEmbedding Z := T.isClosedEmbedding.comp hX
  have hc := orthogonal_affine_harmonic_charts X hchart A.frame A.orthogonal A.offset
  have hr (u v : Fin 3 → ℝ) : R u ⬝ᵥ R v = u ⬝ᵥ v := by
    simpa only [R,LinearEquiv.apply_symm_apply] using (A.orthogonal (R u) (R v)).symm
  have he : (fun x => P+R (Z x)) = X := by
    funext x
    simp [P,R,Z]
  have him : (fun p => P+R p) '' range Z = range X := by
    rw [← range_comp]
    exact congrArg range he
  have h₁ := A.approaching.affine_image R.toContinuousLinearEquiv.toContinuousLinearMap P
  change ApproachesSetAtInfinity ((fun p => P+R p) '' range (axisRuledHelicoid I A.pitch 0)) ((fun p => P+R p) '' range Z) at h₁
  rw [him] at h₁
  obtain ⟨L,f,Y,hfhol,hihol,hf,hclose,him',hreg,_,hh,_,hg⟩ := original_rotated_exterior_marked_torus_reduction top uniform
    Z hZ hc A.exterior R hr P α A.pitch hα A.nonzero (he.symm ▸ h₁) (he.symm ▸ hend)
  exact ⟨L,f,Y,hfhol,hihol,fun x => (hf x).trans (congrFun he x),hclose,him'.trans (congrArg range he),hreg,hh,hg⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_surface_from_arbitrary_exterior_frame
