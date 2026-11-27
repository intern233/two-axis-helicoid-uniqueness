import TwoAxisHelicoid.ChartWeierstrassData
import TwoAxisHelicoid.PrincipalPartExtraPoles

namespace TwoAxisHelicoid
open Complex Set Metric
open HolomorphicCoefficientDisks
set_option maxHeartbeats 1000000

namespace MeromorphicPairInCharts
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [CompactSpace M] [PreconnectedSpace M]

/-- Compare actual height differentials on the common regular locus. Extra
removed Gauss zeros do not weaken the compact real-normalization argument. -/
theorem actual_heights_equal (D : MeromorphicPairInCharts M)
    {P : Set M} (hP : P.Finite) (hsub : chartPoleSet D.left ⊆ P)
    (X Y : ChartWeierstrassData M Pᶜ)
    (hL : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ P → D.left p z = X.height p z)
    (hR : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ P → D.right p z = Y.height p z)
    (p : M) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p))
    (hr : (chartAt ℂ p).symm z ∉ P) : Y.height p z = X.height p z := by
  have hPL : D.common.difference.ZeroRealAvoidingPeriods Pᶜ D.left := by
    intro x c
    rw [c.integral_congr hL]
    exact X.height_zero_real_periods D.common.difference x c
  have hPR : D.common.difference.ZeroRealAvoidingPeriods Pᶜ D.right := by
    intro x c
    rw [c.integral_congr hR]
    exact Y.height_zero_real_periods D.common.difference x c
  have he := D.common.coefficients_equal_avoiding_extra_poles hP hsub hPL hPR p hz hr
  exact (hR p z hz hr).symm.trans (he.symm.trans (hL p z hz hr))

/-- Actual logarithmic Gauss differentials with the same principal parts
agree. Their real periods follow from single-valuedness of the Gauss maps. -/
theorem actual_log_gauss_equal (D : MeromorphicPairInCharts M)
    {P : Set M} (hP : P.Finite) (hsub : chartPoleSet D.left ⊆ P)
    (X Y : ChartWeierstrassData M Pᶜ)
    (hL : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ P → D.left p z = chartLogDerivative X.gauss p z)
    (hR : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ P → D.right p z = chartLogDerivative Y.gauss p z)
    (p : M) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p))
    (hr : (chartAt ℂ p).symm z ∉ P) : chartLogDerivative Y.gauss p z = chartLogDerivative X.gauss p z := by
  have hPL : D.common.difference.ZeroRealAvoidingPeriods Pᶜ D.left := by
    intro x c
    rw [c.integral_congr hL]
    exact chartLogDerivative_zero_real_periods (A := D.common.difference)
      (fun p z hz hu => X.gauss_analytic p z (D.common.difference.ball_target p hz) hu) X.gauss_ne_zero x c
  have hPR : D.common.difference.ZeroRealAvoidingPeriods Pᶜ D.right := by
    intro x c
    rw [c.integral_congr hR]
    exact chartLogDerivative_zero_real_periods (A := D.common.difference)
      (fun p z hz hu => Y.gauss_analytic p z (D.common.difference.ball_target p hz) hu) Y.gauss_ne_zero x c
  have he := D.common.coefficients_equal_avoiding_extra_poles hP hsub hPL hPR p hz hr
  exact (hR p z hz hr).symm.trans (he.symm.trans (hL p z hz hr))

/-- The complete analytic implication in fixed-principal-part rigidity:
actual single-valued coordinates and equal Laurent principal parts yield an
actual global rigid motion. The nonzero horizontal period is the remaining
geometric flux input; it is stated explicitly. -/
theorem actual_fixed_principal_parts_rigid_motion [Nonempty M]
    (DH DG : MeromorphicPairInCharts M)
    (X Y : ChartWeierstrassData M (chartPoleSet DH.left ∪ chartPoleSet DG.left)ᶜ)
    (hHL : ∀ p z, z ∈ ball (chartAt ℂ p p) (DH.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet DH.left ∪ chartPoleSet DG.left → DH.left p z = X.height p z)
    (hHR : ∀ p z, z ∈ ball (chartAt ℂ p p) (DH.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet DH.left ∪ chartPoleSet DG.left → DH.right p z = Y.height p z)
    (hGL : ∀ p z, z ∈ ball (chartAt ℂ p p) (DG.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet DH.left ∪ chartPoleSet DG.left →
      DG.left p z = chartLogDerivative X.gauss p z)
    (hGR : ∀ p z, z ∈ ball (chartAt ℂ p p) (DG.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet DH.left ∪ chartPoleSet DG.left →
      DG.right p z = chartLogDerivative Y.gauss p z)
    {x : M} (c : (DH.regularLeft.commonDisks DG.regularLeft).AvoidingPath
      (chartPoleSet DH.left ∪ chartPoleSet DG.left)ᶜ x x)
    (hA : c.integral (weightedGaussCoefficient X.gauss X.height) ≠ 0)
    {S : Set M} (hS : (chartPoleSet DH.left ∪ chartPoleSet DG.left)ᶜ ⊆ S)
    (hX : ContinuousOn X.position S) (hY : ContinuousOn Y.position S) :
    ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, ∀ x ∈ S,
      Y.position x = verticalRotation (exp ((θ : ℂ)*I)) (X.position x)+b := by
  have hP := DH.poles_finite.union DG.poles_finite
  have hh p (z : ℂ) hz hr := DH.actual_heights_equal hP subset_union_left X Y hHL hHR p (z := z)
    (DH.regularLeft.commonDisks_mem_left DG.regularLeft p hz) hr
  have hg p (z : ℂ) hz hr := DG.actual_log_gauss_equal hP subset_union_right X Y hGL hGR p (z := z)
    (DH.regularLeft.commonDisks_mem_right DG.regularLeft p hz) hr
  obtain ⟨θ,b,hb⟩ := X.rigid_motion_of_log_derivative hP Y
    (DH.regularLeft.commonDisks DG.regularLeft) hh hg c hA
  exact ⟨θ,b,ChartWeierstrassData.rigid_motion_extends hP hS hX hY _ b hb⟩

end MeromorphicPairInCharts
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.actual_heights_equal
#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.actual_log_gauss_equal
#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.actual_fixed_principal_parts_rigid_motion
