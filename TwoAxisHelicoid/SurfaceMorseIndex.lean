import TwoAxisHelicoid.ExteriorChartTestFunctions
import TwoAxisHelicoid.OrthogonalAreaVariation

namespace TwoAxisHelicoid
open Complex Set Function Filter Matrix MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

/-- Infinite Morse index expressed through genuine compact spatial
variations of a parametrized surface. The area is measured in its chart
on the common compact patch. Every variation is stationary on the entire
complement of that patch. -/
def HasInfiniteCompactSurfaceMorseIndex {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) : Prop :=
  ∀ C : Set M, IsCompact C → ∀ n : ℕ, ∃ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (K : Set (ℝ × ℝ))
    (U : Fin n → M → ℝ) (N : M → Fin 3 → ℝ),
    let P := e.symm '' (translatedPlaneCoordinates c '' K)
    let ξ := fun z : ℂ => e.symm (z+c)
    let V := fun (i : Fin n) (x : M) => U i x • N x
    let variation := fun (a : Fin n → ℝ) (s : ℝ) (x : M) => X x+s • ((∑ i, a i*U i x) • N x)
    e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ IsCompact K ∧ (∀ p ∈ K, translatedPlaneCoordinates c p ∈ e.target) ∧ IsCompact P ∧ Disjoint P C ∧
    (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (U i) ∧ tsupport (U i) ⊆ P) ∧ LinearIndependent ℝ U ∧
    (∀ p ∈ K, (N (ξ (planeComplex p)) ⬝ᵥ N (ξ (planeComplex p))) = 1 ∧
      ∀ w : ℂ, N (ξ (planeComplex p)) ⬝ᵥ fderiv ℝ (X ∘ ξ) (planeComplex p) w = 0) ∧
    (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (V i)) ∧ LinearIndependent ℝ V ∧
    (∀ a s x, x ∉ P → variation a s x = X x) ∧
    ∀ a : Fin n → ℝ, a ≠ 0 → deriv (deriv (fun s : ℝ => ∫ p in K,
      coordinateAreaDensity (variation a s ∘ ξ) (planeComplex p))) 0 < 0

theorem independent_compact_normal_multiples {M : Type*} [TopologicalSpace M] {n : ℕ}
    (U : Fin n → M → ℝ) (N : M → Fin 3 → ℝ) {P : Set M}
    (hl : LinearIndependent ℝ U) (ht : ∀ i, tsupport (U i) ⊆ P) (hN : ∀ x ∈ P, N x ≠ 0) :
    LinearIndependent ℝ (fun (i : Fin n) (x : M) => U i x • N x) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  apply Fintype.linearIndependent_iff.mp hl a
  funext x
  change (∑ i, a i • U i) x = 0
  by_cases hx : x ∈ P
  · have h : (∑ i, a i*U i x) • N x = 0 := by
      simpa only [Finset.sum_smul,mul_smul,Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using congrFun ha x
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (smul_eq_zero.mp h).resolve_right (hN x hx)
  · have hz (i : Fin n) : U i x = 0 := by
      by_contra h
      exact hx (ht i (subset_closure h))
    simp [Finset.sum_apply,hz]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.independent_compact_normal_multiples
