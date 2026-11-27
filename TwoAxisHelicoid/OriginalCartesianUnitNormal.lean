import TwoAxisHelicoid.RegularOriginalSurfaceNormals

namespace TwoAxisHelicoid
open Set Matrix Topology
open scoped Manifold RealInnerProductSpace

/-- The geometric surface has a continuous Cartesian unit normal orthogonal
to the actual differential in its original real chart at every point. -/
theorem OriginalSmoothHelicoid.exists_cartesian_unit_normal (s : OriginalSmoothHelicoid) :
    ∃ N : s.carrier → Fin 3 → ℝ, Continuous N ∧ (∀ p, N p ⬝ᵥ N p = 1) ∧
      ∀ p v, fderiv ℝ (s.position ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) v ⬝ᵥ N p = 0 := by
  obtain ⟨m,cm,unit,bundle,_⟩ := original_smooth_regular_normal_geometry s
  let N := fun p => surfaceCartesianEquiv (m p)
  have inner (a b : Fin 3 → ℝ) : ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫ = a ⬝ᵥ b := by
    rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,
      star_trivial,dotProduct_comm]
  have eq (p : s.carrier) : coordinateToEuclidean (N p) = m p := surfaceEuclidean_toCartesian _
  refine ⟨N,surfaceCartesianEquiv.continuous.comp cm,?_,?_⟩
  · intro p
    rw [← inner,eq,real_inner_self_eq_norm_sq,unit,one_pow]
  · intro p v
    have member : (s.euclideanPosition p,m p) ∈ s.unorientedNormals := by
      rw [bundle]
      exact ⟨p,rfl,Or.inl rfl⟩
    obtain ⟨q,pos,_,orth⟩ := member
    have same : q = p := (surfaceCartesianEquiv.symm.injective.comp s.closedEmbedding.injective) pos
    subst q
    rw [← inner,eq]
    exact orth _ ⟨v,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.exists_cartesian_unit_normal
