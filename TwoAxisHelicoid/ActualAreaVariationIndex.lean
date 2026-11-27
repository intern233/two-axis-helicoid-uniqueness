import TwoAxisHelicoid.AnalyticCompactAreaVariation
import TwoAxisHelicoid.CoordinateAreaIndex

namespace TwoAxisHelicoid
open Complex Set Filter Function Bornology MeasureTheory
open scoped Topology ContDiff

set_option maxHeartbeats 1500000
attribute [local irreducible] coordinateVariationDensity gaussNormalDirichletDensity
  nullRealDerivative weierstrassTriple infinityCorrection

/-- Negative spaces for the second derivative of the actual finite-patch
area integral, with a common compact patch for every vector in the space. -/
def HasInfiniteCompactActualAreaIndexAtInfinity
    (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ) : Prop :=
  ∀ R : ℝ, ∀ n : ℕ, ∃ (K : Set (ℝ × ℝ)) (v : Fin n → ℝ × ℝ → ℝ),
    IsCompact K ∧ (∀ p ∈ K, R < ‖p‖) ∧
    (∀ i, ContDiff ℝ ∞ (v i) ∧ tsupport (v i) ⊆ K) ∧ LinearIndependent ℝ v ∧
    ∀ c : Fin n → ℝ, c ≠ 0 →
      deriv (deriv (fun s : ℝ => ∫ p in K,
        coordinateVariationDensity X W (fun p => ∑ i, c i*v i p) s p)) 0 < 0

theorem finite_test_sum_tsupport_subset {n : ℕ} {v : Fin n → ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hv : ∀ i, tsupport (v i) ⊆ K) (c : Fin n → ℝ) :
    tsupport (fun p => ∑ i, c i*v i p) ⊆ K := by
  apply closure_minimal ?_ hK
  intro p hp
  by_contra hnot
  apply hp
  apply Finset.sum_eq_zero
  intro i _
  have hz : v i p = 0 := by
    by_contra hn
    exact hnot (hv i (subset_closure hn))
  rw [hz,mul_zero]

/-- The analytic helicoidal end has infinite negative index for actual
compact normal area variations, including the justified integral second
derivative rather than only the integral of pointwise Hessians. -/
theorem analytic_helicoid_actual_area_infinite_index
    {α : ℝ} (hα : α ≠ 0) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0)
    {X : ℂ → Fin 3 → ℝ} {B : ℝ}
    (hX : ∀ p : ℝ × ℝ, B ≤ ‖p‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple
        (exp (I*(α : ℂ)*planeComplex p+infinityCorrection f (planeComplex p))) 1))
      (planeComplex p)) :
    HasInfiniteCompactActualAreaIndexAtInfinity X
      (fun z => I*(α : ℂ)*z+infinityCorrection f z) := by
  obtain ⟨A,_,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (infinityCorrection_eventually_analytic hf)
  have hi := analytic_helicoid_gauss_normal_infinite_index hα hf h0
  intro R n
  let T := max R (max B A)
  obtain ⟨v,hv,hfar,hlin,hneg⟩ := hi T n
  let K := ⋃ i : Fin n, tsupport (v i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hv i).2)
  have hsupport i : tsupport (v i) ⊆ K := subset_iUnion (fun i => tsupport (v i)) i
  have hfarK p (hp : p ∈ K) : T < ‖p‖ := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    exact hfar i p hi
  refine ⟨K,v,hK,(fun p hp => (le_max_left _ _).trans_lt (hfarK p hp)),
    (fun i => ⟨(hv i).1,hsupport i⟩),hlin,?_⟩
  intro c hc
  have hvc : ContDiff ℝ ∞ (fun p => ∑ i, c i*v i p) := by
    have hvi (i : Fin n) : ContDiff ℝ ∞ (v i) := (hv i).1
    fun_prop
  have hw (p : ℝ × ℝ) (hp : p ∈ K) :
      AnalyticAt ℂ (fun z => I*(α : ℂ)*z+infinityCorrection f z) (planeComplex p) := by
    have hAp : A ≤ ‖planeComplex p‖ :=
      (le_max_right B A).trans ((le_max_right R (max B A)).trans
        ((hfarK p hp).le.trans (norm_le_planeComplex_norm p)))
    exact (analyticAt_const.mul analyticAt_id).add (hA hAp)
  have hd := compact_actual_area_second_variation_of_analytic_data
    (X := X) (W := fun z => I*(α : ℂ)*z+infinityCorrection f z)
    (v := fun p => ∑ i, c i*v i p) hK
    (finite_test_sum_tsupport_subset hK.isClosed hsupport c) hvc
    (fun p hp => hX p ((le_max_left B A).trans
      ((le_max_right R (max B A)).trans (hfarK p hp).le)))
    hw
  exact hd.deriv.trans_lt (hneg c hc)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoid_actual_area_infinite_index
