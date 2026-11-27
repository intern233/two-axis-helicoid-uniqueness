import TwoAxisHelicoid.SurfaceMorseIndex

namespace TwoAxisHelicoid
open Set Complex Matrix MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

/-- Rigid changes of the ambient frame preserve the negative spaces
for actual area variations on the same compact chart patches. -/
theorem surface_morse_index_of_orthogonal_affine {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ)
    (ortho : ∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y)
    (index : HasInfiniteCompactSurfaceMorseIndex (fun x => b+T (X x))) :
    HasInfiniteCompactSurfaceMorseIndex X := by
  let Z := fun x => b+T (X x)
  intro C hC n
  obtain ⟨e,c,K,U,N,hol,hK,ht,hP,dis,hu,ind,normals,smooth,_,_,neg⟩ := index C hC n
  let ξ := fun z : ℂ => e.symm (z+c)
  let P := e.symm '' (translatedPlaneCoordinates c '' K)
  let N' := T.symm ∘ N
  have tf (x) : T (N' x)=N x := T.apply_symm_apply _
  have unit p (hp : p∈K) : N' (ξ (planeComplex p)) ⬝ᵥ N' (ξ (planeComplex p))=1 := by rw [← ortho,tf]; exact (normals p hp).1
  have nn x (hx : x∈P) : N' x≠0 := by
    obtain ⟨_,⟨p,hp,rfl⟩,rfl⟩ := hx
    rw [translatedPlaneCoordinates_apply]
    intro zero
    change N' (ξ (planeComplex p))=0 at zero
    have one := unit p hp
    rw [zero,zero_dotProduct] at one
    exact zero_ne_one one
  refine ⟨e,c,K,U,N',hol,hK,ht,hP,dis,hu,ind,?_,?_,independent_compact_normal_multiples U N' ind (fun i => (hu i).2) nn,?_,?_⟩
  · intro p hp
    refine ⟨unit p hp,fun w => ?_⟩
    have map : fderiv ℝ (Z ∘ ξ) (planeComplex p) w=T (fderiv ℝ (X ∘ ξ) (planeComplex p) w) := by
      change fderiv ℝ (fun z => b+T ((X ∘ ξ) z)) (planeComplex p) w=_
      rw [fderiv_const_add]
      change fderiv ℝ (T ∘ (X ∘ ξ)) (planeComplex p) w=_
      rw [T.comp_fderiv]
      rfl
    rw [← ortho,tf,← map]
    exact (normals p hp).2 w
  · intro i
    apply (T.symm.toContinuousLinearMap.contMDiff.comp (smooth i)).congr
    exact fun x => (T.symm.map_smul (U i x) (N x)).symm
  · intro a s x hx
    have zero (i : Fin n) : U i x=0 := by by_contra h; exact hx ((hu i).2 (subset_closure h))
    simp [zero]
  · intro a na
    have area (s : ℝ) : (∫ p in K,coordinateAreaDensity ((fun x => X x+s • ((∑ i,a i*U i x) • N' x)) ∘ ξ) (planeComplex p))=
        ∫ p in K,coordinateAreaDensity ((fun x => Z x+s • ((∑ i,a i*U i x) • N x)) ∘ ξ) (planeComplex p) := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p _
      refine (coordinate_area_orthogonal_affine T ortho b _ (planeComplex p)).symm.trans ?_
      apply congrArg (fun F => coordinateAreaDensity F (planeComplex p))
      funext z
      exact orthogonal_affine_normal_variation T b X N (fun x => ∑ i,a i*U i x) s (ξ z)
    change deriv (deriv _) 0<0
    rw [funext area]
    exact neg a na

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_morse_index_of_orthogonal_affine
