import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.CoordinateOrientationIsometry
import Mathlib.Analysis.Normed.Affine.MazurUlam

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Topology
open scoped Topology ContDiff Manifold RealInnerProductSpace

/-- A concrete Euclidean isometry in spatial coordinates is a translation
followed by a single orthogonal linear coordinate map. -/
theorem orthogonal_affine_coordinates_of_displacement (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j - R w j)^2) = ∑ j, (v j-w j)^2) :
    ∃ (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ),
       (∀ v w, T v ⬝ᵥ T w = v ⬝ᵥ w) ∧ ∀ v, R v = b+T v := by
  let E := (euclideanOrientationIsometry R hR).toRealAffineIsometryEquiv
  let C := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ))
  let T := (C.symm.trans E.linearIsometryEquiv.toLinearEquiv).trans C
  have hdot (v w : EuclideanSpace ℝ (Fin 3)) : ⟪v,w⟫ = C v ⬝ᵥ C w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]
    rfl
  refine ⟨T,R 0,?_,?_⟩
  · intro v w
    change C (E.linearIsometryEquiv (C.symm v)) ⬝ᵥ C (E.linearIsometryEquiv (C.symm w)) = _
    rw [← hdot,E.linearIsometryEquiv.inner_map_map,hdot,C.apply_symm_apply,C.apply_symm_apply]
  · intro v
    have he := E.map_vadd (0 : EuclideanSpace ℝ (Fin 3)) (C.symm v)
    change E (C.symm v+0) = E.linearIsometryEquiv (C.symm v)+E 0 at he
    rw [add_zero] at he
    exact (congrArg C he).trans (add_comm _ _)

/-- Pull back the actual height and Gauss chart by a biholomorphic marking
and a pointwise equality of the spatial positions. -/
theorem geometric_exterior_coordinate_pullback {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]
    (h : M ≃ₜ N) (hh : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h)
    (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.symm)
    {X : M → Fin 3 → ℝ} {Y : N → Fin 3 → ℝ} (hm : ∀ x, Y (h x) = X x)
    (A : GeometricExteriorCoordinate Y) : Nonempty (GeometricExteriorCoordinate X) := by
  let d := h.toOpenPartialHomeomorph.trans A.chart
  have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact ((contMDiffAt_of_mem_maximalAtlas A.holomorphic hx.2).comp x hh.contMDiffAt).contMDiffWithinAt
    · intro z hz
      exact (hi.contMDiffAt.comp z (contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic hz.1)).contMDiffWithinAt
  have hc : d.sourceᶜ = h.symm '' A.chart.sourceᶜ := by
    ext x
    change ¬(x ∈ univ ∧ h x ∈ A.chart.source) ↔ _
    rw [h.symm.image_eq_preimage_symm]
    simp
  have ht : d.target = A.chart.target := by ext z; change (_ ∧ _ ∈ univ) ↔ _; simp
  have he (z : ℂ) : X (d.symm z) = Y (A.chart.symm z) := by
    change X (h.symm (A.chart.symm z)) = _
    rw [← hm,h.apply_symm_apply]
  refine ⟨⟨d,A.radius,A.positive,ht.trans A.target,hc ▸ A.core.image h.symm.continuous,hd,
    A.heightOffset,?_,A.pitch,A.pitch_ne,A.correction,A.analytic,?_⟩⟩
  · intro x hx
    rw [← hm]
    exact A.height (h x) hx.2
  · have heq : X ∘ d.symm = Y ∘ A.chart.symm := funext he
    rw [heq]
    exact A.gauss

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orthogonal_affine_coordinates_of_displacement
#print axioms TwoAxisHelicoid.geometric_exterior_coordinate_pullback
