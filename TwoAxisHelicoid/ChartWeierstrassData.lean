import TwoAxisHelicoid.ChartWeierstrassPeriods
import TwoAxisHelicoid.ChartPrimitiveRigidity
import TwoAxisHelicoid.GaussQuotientRigidity

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 1000000

/-- Actual single-valued coordinates and their Weierstrass differential in
every chart, on a specified regular locus. Period closure and rigidity are
conclusions, not fields of this data. -/
structure ChartWeierstrassData (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
    (U : Set M) where
  position : M → Fin 3 → ℝ
  gauss : M → ℂ
  height : M → ℂ → ℂ
  gauss_analytic : ∀ p z, z ∈ (chartAt ℂ p).target → (chartAt ℂ p).symm z ∈ U →
    AnalyticAt ℂ (fun w : ℂ => gauss ((chartAt ℂ p).symm w)) z
  gauss_ne_zero : ∀ x ∈ U, gauss x ≠ 0
  height_continuous : ∀ p z, z ∈ (chartAt ℂ p).target → (chartAt ℂ p).symm z ∈ U →
    ContinuousAt (height p) z
  differential : ∀ p z, z ∈ (chartAt ℂ p).target → (chartAt ℂ p).symm z ∈ U →
    HasFDerivAt (fun w : ℂ => position ((chartAt ℂ p).symm w))
      (nullRealDerivative (weierstrassTriple (gauss ((chartAt ℂ p).symm z)) (height p z))) z

namespace ChartWeierstrassData
open HolomorphicCoefficientDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

theorem height_zero_real_periods {U : Set M} (X : ChartWeierstrassData M U)
    (A : HolomorphicCoefficientDisks M) : A.ZeroRealAvoidingPeriods U X.height := by
  intro x c
  have h := c.scalar_real_integral
    (fun p z hz hu => X.height_continuous p z (A.ball_target p hz) hu)
    (H := fun x => X.position x 2) (by
      intro p z hz hu
      exact (ContinuousLinearMap.proj 2).hasFDerivAt.comp z
        (X.differential p z (A.ball_target p hz) hu))
  simpa only [sub_self] using h

theorem horizontal_periods_close {U : Set M} (X : ChartWeierstrassData M U)
    {A : HolomorphicCoefficientDisks M} {x : M} (c : A.AvoidingPath U x x) :
    HorizontalLinePeriodsClose c X.gauss X.height :=
  actual_weierstrass_horizontal_periods_close
    (fun p z hz hu => (X.gauss_analytic p z (A.ball_target p hz) hu).continuousAt)
    X.gauss_ne_zero
    (fun p z hz hu => X.height_continuous p z (A.ball_target p hz) hu)
    (fun p z hz hu => X.differential p z (A.ball_target p hz) hu) c

/-- A nonzero actual horizontal period rules out changing the modulus of
the Gauss multiplier. The single-valued maps themselves supply closure. -/
theorem rigid_motion_of_proportional [PreconnectedSpace M] [Nonempty M]
    {P : Set M} (hP : P.Finite) (X Y : ChartWeierstrassData M Pᶜ)
    (A : HolomorphicCoefficientDisks M)
    (hheight : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      Y.height p z = X.height p z)
    {k : ℂ} (hk : k ≠ 0) (hg : ∀ x ∉ P, Y.gauss x = k*X.gauss x)
    {x : M} (c : A.AvoidingPath Pᶜ x x)
    (hA : c.integral (weightedGaussCoefficient X.gauss X.height) ≠ 0) :
    ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, ∀ x ∉ P,
      Y.position x = verticalRotation (exp ((θ : ℂ)*I)) (X.position x)+b := by
  have hY (p : M) (z : ℂ) (hz : z ∈ ball (chartAt ℂ p p) (A.radius p))
      (hu : (chartAt ℂ p).symm z ∉ P) : HasFDerivAt (fun w : ℂ => Y.position ((chartAt ℂ p).symm w))
      (nullRealDerivative (weierstrassTriple (Y.gauss ((chartAt ℂ p).symm z)) (X.height p z))) z := by
    simpa only [hheight p z hz hu] using Y.differential p z (A.ball_target p hz) hu
  have hcY := actual_weierstrass_horizontal_periods_close
    (fun p z hz hu => (Y.gauss_analytic p z (A.ball_target p hz) hu).continuousAt)
    Y.gauss_ne_zero
    (fun p z hz hu => X.height_continuous p z (A.ball_target p hz) hu) hY c
  have hk1 := actual_horizontal_closed_multiplier_norm_one c X.height hk hg hA
    (X.horizontal_periods_close c) hcY
  obtain ⟨b,hb⟩ := A.chart_weierstrass_primitives_unit_multiplier hP hk1
    (fun p z hz hu => X.differential p z (A.ball_target p hz) hu) (by
      intro p z hz hu
      simpa only [hg _ hu] using hY p z hz hu)
  have he := Complex.norm_mul_exp_arg_mul_I k
  rw [hk1,Complex.ofReal_one,one_mul] at he
  exact ⟨arg k,b,fun x hx => by simpa only [he] using hb x hx⟩

/-- The logarithmic derivative hypothesis is an equality of actual local
Gauss derivatives; a global multiplier is derived on the punctured curve. -/
theorem rigid_motion_of_log_derivative [PreconnectedSpace M] [Nonempty M]
    {P : Set M} (hP : P.Finite) (X Y : ChartWeierstrassData M Pᶜ)
    (A : HolomorphicCoefficientDisks M)
    (hheight : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      Y.height p z = X.height p z)
    (hlog : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      chartLogDerivative Y.gauss p z = chartLogDerivative X.gauss p z)
    {x : M} (c : A.AvoidingPath Pᶜ x x)
    (hA : c.integral (weightedGaussCoefficient X.gauss X.height) ≠ 0) :
    ∃ θ : ℝ, ∃ b : Fin 3 → ℝ, ∀ x ∉ P,
      Y.position x = verticalRotation (exp ((θ : ℂ)*I)) (X.position x)+b := by
  obtain ⟨k,hk,hg⟩ := A.gauss_maps_proportional_of_log_derivative_eq hP
    (fun p z hz hu => X.gauss_analytic p z (A.ball_target p hz) hu)
    (fun p z hz hu => Y.gauss_analytic p z (A.ball_target p hz) hu)
    X.gauss_ne_zero Y.gauss_ne_zero
    hlog
  exact X.rigid_motion_of_proportional hP Y A hheight hk hg c hA

/-- Extend the actual rigid motion through removable Gauss zeros and poles.
Only continuity of the coordinate maps at those ordinary surface points is
used; a genuine end need not be part of `S`. -/
theorem rigid_motion_extends {P S : Set M} (hP : P.Finite) (hPS : Pᶜ ⊆ S)
    {X Y : M → Fin 3 → ℝ} (hX : ContinuousOn X S) (hY : ContinuousOn Y S)
    (k : ℂ) (b : Fin 3 → ℝ)
    (h : ∀ x ∉ P, Y x = verticalRotation k (X x)+b) :
    ∀ x ∈ S, Y x = verticalRotation k (X x)+b := by
  apply Set.EqOn.of_subset_closure (s := Pᶜ) h hY
    (((verticalRotation k).continuous.comp_continuousOn hX).add continuousOn_const) hPS
  intro x _hx
  exact finite_compl_dense_complex_charts hP x

end ChartWeierstrassData
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ChartWeierstrassData.height_zero_real_periods
#print axioms TwoAxisHelicoid.ChartWeierstrassData.rigid_motion_of_log_derivative
#print axioms TwoAxisHelicoid.ChartWeierstrassData.rigid_motion_extends
