import TwoAxisHelicoid.EmbeddedTorusSimilarityFields
import TwoAxisHelicoid.TorusJacobiDescent
import Mathlib.LinearAlgebra.StdBasis

namespace TwoAxisHelicoid
open Complex Set Matrix Filter Topology InnerProductSpace
open scoped Topology

/-- Three translations, three infinitesimal rotations about coordinate
axes, and dilation, with independent real coefficients. -/
noncomputable def sevenSimilarityNormalMap (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ) :
    (Fin 7 → ℝ) →ₗ[ℝ] (PuncturedPeriodTorus L → ℝ) where
  toFun p q := markedSimilarityJacobiField L X ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) q.1
  map_add' p q := by
    funext z
    obtain ⟨w,rfl⟩ := puncturedPlaneProjection_surjective L z
    simp only [Pi.add_apply]
    change similarityNormal _ _ _ _ _ w.1 = similarityNormal _ _ _ _ _ w.1 + similarityNormal _ _ _ _ _ w.1
    unfold similarityNormal similarityField
    simp [Fin.sum_univ_succ,cross_apply]
    ring
  map_smul' t p := by
    funext z
    obtain ⟨w,rfl⟩ := puncturedPlaneProjection_surjective L z
    change similarityNormal _ _ _ _ _ w.1 = t*similarityNormal _ _ _ _ _ w.1
    unfold similarityNormal similarityField
    simp [Fin.sum_univ_succ,cross_apply]
    ring

/-- The actual seven fields on the punctured quotient are linearly
independent smooth Jacobi fields. -/
theorem seven_geometric_jacobi_fields (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    let J := sevenSimilarityNormalMap L X
    Function.Injective J ∧
      LinearIndependent ℝ (fun i : Fin 7 => J (Pi.basisFun ℝ (Fin 7) i)) ∧
      ∀ p, IsSmoothMarkedJacobiField L X (J p) := by
  let J := sevenSimilarityNormalMap L X
  have hz (p : Fin 7 → ℝ) (hp : J p = 0) : p = 0 := by
    obtain ⟨ha,hb,hd⟩ := embedded_torus_similarity_normal_independent L X hX (fun z h =>
      ⟨analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hY z h).1 j)),(hY z h).2⟩)
      ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (fun z h => congrFun hp (puncturedPlaneProjection L ⟨z,h⟩))
    funext i
    fin_cases i
    · exact congrFun ha 0
    · exact congrFun ha 1
    · exact congrFun ha 2
    · exact congrFun hb 0
    · exact congrFun hb 1
    · exact congrFun hb 2
    · exact hd
  have hi : Function.Injective J := by
    intro p q he
    apply sub_eq_zero.mp
    exact hz (p-q) (by rw [map_sub,he,sub_self])
  exact ⟨hi,(Pi.basisFun ℝ (Fin 7)).linearIndependent.map' J (LinearMap.ker_eq_bot.mpr hi),
    fun p => markedSimilarityJacobiField_isJacobi L X hY _ _ _⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.seven_geometric_jacobi_fields
