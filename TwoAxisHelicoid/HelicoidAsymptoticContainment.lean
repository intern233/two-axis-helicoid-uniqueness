import TwoAxisHelicoid.AxisHelicoidGauge
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Metric Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1100000

/-- For every prescribed spatial distance, all sufficiently distant
points of S lie within that distance of T. This is the one-sided
half of vanishing Hausdorff distance on ends. -/
def ApproachesSetAtInfinity {E : Type*} [NormedAddCommGroup E] (S T : Set E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x ∈ S, R ≤ ‖x‖ → ∃ y ∈ T, dist x y < ε

theorem ApproachesSetAtInfinity.trans {E : Type*} [NormedAddCommGroup E] {S T U : Set E}
    (h₁ : ApproachesSetAtInfinity S T) (h₂ : ApproachesSetAtInfinity T U) :
    ApproachesSetAtInfinity S U := by
  intro ε hε
  obtain ⟨R,hR⟩ := h₁ (ε/2) (half_pos hε)
  obtain ⟨K,hK⟩ := h₂ (ε/2) (half_pos hε)
  refine ⟨max R (K+ε/2),?_⟩
  intro x hx hnorm
  obtain ⟨y,hy,hxy⟩ := hR x hx ((le_max_left _ _).trans hnorm)
  have hk' := (le_max_right R (K+ε/2)).trans hnorm
  have hdist := norm_sub_norm_le x y
  rw [← dist_eq_norm] at hdist
  obtain ⟨z,hz,hyz⟩ := hK y hy (by linarith)
  exact ⟨z,hz,(dist_triangle x y z).trans_lt (by linarith)⟩

theorem ApproachesSetAtInfinity.exists_sequence {E : Type*} [NormedAddCommGroup E]
    {S T : Set E} (h : ApproachesSetAtInfinity S T) (hne : T.Nonempty)
    {p : ℕ → E} (hp : ∀ n, p n ∈ S) (hes : Tendsto (fun n => ‖p n‖) atTop atTop) :
    ∃ q : ℕ → E, (∀ n, q n ∈ T) ∧ Tendsto (fun n => q n-p n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => infDist (p n) T) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R,hR⟩ := h ε hε
    filter_upwards [hes.eventually_ge_atTop R] with n hn
    obtain ⟨y,hy,hd⟩ := hR _ (hp n) hn
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg infDist_nonneg] using (infDist_le_dist_of_mem hy).trans_lt hd
  have hq (n : ℕ) : ∃ y ∈ T, dist (p n) y < infDist (p n) T+1/((n:ℝ)+1) :=
    (infDist_lt_iff hne).mp (lt_add_of_pos_right _ (by positivity))
  choose q hqt hqd using hq
  refine ⟨q,hqt,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  apply squeeze_zero (g := fun n : ℕ => infDist (p n) T+1/((n:ℝ)+1)) (fun _ => norm_nonneg _)
  · intro n
    rw [← dist_eq_norm,dist_comm]
    exact (hqd n).le
  · simpa only [zero_add] using hlim.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Coordinate-free form of the same one-sided closeness: an ambient
continuous linear equivalence preserves vanishing distance at infinity.
This transports the Euclidean and coordinate sup-norm formulations. -/
theorem ApproachesSetAtInfinity.continuousLinearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S T : Set E} (h : ApproachesSetAtInfinity S T) (L : E ≃L[ℝ] F) :
    ApproachesSetAtInfinity (L '' S) (L '' T) := by
  let C := ‖(L : E →L[ℝ] F)‖+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (x : E) : ‖L x‖ ≤ C*‖x‖ :=
    ((L : E →L[ℝ] F).le_opNorm x).trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  intro ε hε
  obtain ⟨R,hR⟩ := h (ε/C) (div_pos hε hC)
  refine ⟨C*R,?_⟩
  rintro _ ⟨x,hx,rfl⟩ hh
  obtain ⟨y,hy,hxy⟩ := hR x hx ((mul_le_mul_iff_right₀ hC).mp (hh.trans (hbound x)))
  refine ⟨L y,⟨y,hy,rfl⟩,?_⟩
  rw [dist_eq_norm] at hxy ⊢
  rw [← map_sub]
  exact (hbound _).trans_lt (by have := (lt_div_iff₀ hC).mp hxy; linarith)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ApproachesSetAtInfinity.exists_sequence
