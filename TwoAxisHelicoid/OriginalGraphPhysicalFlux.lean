import TwoAxisHelicoid.PlacedBasicHorizontalFlux
import TwoAxisHelicoid.OriginalGraphUniformizationRigidity
import TwoAxisHelicoid.ActualTorusRigidityHypotheses
import TwoAxisHelicoid.GeometricExteriorPullback

namespace TwoAxisHelicoid
open Complex Set Matrix InnerProductSpace
open scoped Topology RealInnerProductSpace

private theorem euclidean_isometry_affine_coefficients
    (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) :
    ∃ (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ), (∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) ∧
      ∀ v, WithLp.ofLp (E (coordinateToEuclidean v))=b+T v := by
  let A := E.toRealAffineIsometryEquiv
  let C := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  let T := (C.symm.trans A.linearIsometryEquiv.toLinearEquiv).trans C
  have dot (v w : EuclideanSpace ℝ (Fin 3)) : ⟪v,w⟫=C v ⬝ᵥ C w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]; rfl
  refine ⟨T,C (E 0),?_,?_⟩
  · intro v w
    change C (A.linearIsometryEquiv (C.symm v)) ⬝ᵥ C (A.linearIsometryEquiv (C.symm w))=_
    rw [← dot,A.linearIsometryEquiv.inner_map_map,dot,C.apply_symm_apply,C.apply_symm_apply]
  · intro v
    have he := A.map_vadd (0:EuclideanSpace ℝ (Fin 3)) (C.symm v)
    change A (C.symm v+0)=A.linearIsometryEquiv (C.symm v)+A 0 at he
    rw [add_zero] at he
    exact (congrArg C he).trans (add_comm _ _)

/-- On the original C¹ two-axis surface the conormal integral on an
actual closed loop has a nonzero horizontal component in its own
physical frame. The ambient similarity is allowed to tilt the axes. -/
theorem original_graph_horizontal_flux_from_uniformization (s : OriginalHelicoidRepresentative)
    (uni : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ (f : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (X : PuncturedPeriodTorus certifiedPeriodPair → Fin 3 → ℝ),
      (∀ p, X (f p)=s.position p) ∧ ∃ (p : s.carrier) (γ : Path p p) (q : PuncturedPeriodTorus certifiedPeriodPair)
      (δ : Path q q) (j : Fin 3) (v : ℝ), (∀ t, f (γ t)=δ t) ∧ (∀ t, X (δ t)=s.position (γ t)) ∧
      j≠2 ∧ v≠0 ∧ TorusSpatialConormalIntegral certifiedPeriodPair X j δ v := by
  obtain ⟨f,k,E,hk,eq⟩ := original_graph_similarity_of_classical_uniformization s uni
  obtain ⟨T,b,ortho,form⟩ := euclidean_isometry_affine_coefficients E.symm
  let V := fun q => WithLp.ofLp (certifiedTorusImmersion q)
  let X := fun q => b+k⁻¹ • T (V q)
  have pos (x : s.carrier) : X (f x)=s.position x := by
    have e : k⁻¹ • certifiedTorusImmersion (f x)=E (s.euclideanPosition x) := by rw [eq,smul_smul,inv_mul_cancel₀ hk.ne',one_smul]
    have a := form (k⁻¹ • V (f x))
    change WithLp.ofLp (E.symm (k⁻¹ • certifiedTorusImmersion (f x)))=b+T (k⁻¹ • V (f x)) at a
    rw [e,E.symm_apply_apply,map_smul] at a
    exact a.symm
  let p := certifiedClosedParameters
  have basic := actual_torus_pulled_coordinate_differential p.height_pos p.abscissa_mem (by norm_num : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have carrier := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  obtain ⟨q,δ,j,v,n,h,vn⟩ := placed_basic_torus_has_horizontal_flux p.height_pos p.abscissa_mem (by norm_num : (1:ℝ)≠0)
    V (fun z hz => (carrier.1 z hz).2) basic T ortho b (inv_ne_zero hk.ne')
  let γ := δ.map f.symm.continuous
  have e (t : unitInterval) : f (γ t)=δ t := f.apply_symm_apply _
  exact ⟨f,X,pos,_,γ,q,δ,j,v,e,fun t => (e t) ▸ pos (γ t),n,vn,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_horizontal_flux_from_uniformization
