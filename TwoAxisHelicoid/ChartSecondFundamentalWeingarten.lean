import TwoAxisHelicoid.EuclideanUnitChartNormal

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- The scalar second fundamental form in arbitrary real surface coordinates:
pair the actual ambient Hessian with the oriented Euclidean unit normal. -/
noncomputable def chartScalarSecondFundamentalForm (Y : ℂ → Fin 3 → ℝ) (z v w : ℂ) : ℝ :=
  iteratedFDeriv ℝ 2 Y z ![v,w] ⬝ᵥ unitCrossNormal (fderiv ℝ Y z 1) (fderiv ℝ Y z I)

private theorem euclidean_cartesian_dot (a b : Fin 3 → ℝ) :
    ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫ = a ⬝ᵥ b := by
  rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]

theorem euclidean_chart_normal_eq_unitCross (Y : ℂ → Fin 3 → ℝ) (z : ℂ) :
    euclideanUnitChartNormal Y z = coordinateToEuclidean (unitCrossNormal (fderiv ℝ Y z 1) (fderiv ℝ Y z I)) := by
  let C := surfaceTangentCross Y z
  have hs : Real.sqrt (C ⬝ᵥ C) = ‖coordinateToEuclidean C‖ := by
    rw [← euclidean_cartesian_dot,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  change ‖coordinateToEuclidean C‖⁻¹ • coordinateToEuclidean C = coordinateToEuclidean ((Real.sqrt (C ⬝ᵥ C))⁻¹ • C)
  rw [hs,map_smul]

private theorem inner_direction_zero_of_constant
    {A D : ℂ → SurfaceEuclideanSpace} {A' D' : ℂ →L[ℝ] SurfaceEuclideanSpace}
    {z : ℂ} (ha : HasFDerivAt A A' z) (hd : HasFDerivAt D D' z) {c : ℝ}
    (hs : (fun x => ⟪A x,D x⟫) =ᶠ[𝓝 z] fun _ => c) (v : ℂ) :
    ⟪A z,D' v⟫+⟪A' v,D z⟫ = 0 := by
  have he := (ha.inner ℝ hd).unique ((hasFDerivAt_const c z).congr_of_eventuallyEq hs)
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) he

/-- Differentiation of a unit normal in an arbitrary coordinate direction is tangent. -/
theorem euclidean_normal_derivative_is_tangent {M : Type*} [TopologicalSpace M]
    {F : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ} (hr : RegularImmersionChart F e)
    {z : ℂ} (hz : z ∈ e.target) (v : ℂ) :
    fderiv ℝ (euclideanUnitChartNormal (F ∘ e.symm)) z v ∈ chartEuclideanTangent F e z := by
  let Y := F ∘ e.symm
  let N := euclideanUnitChartNormal Y
  have hN := (euclideanUnitChartNormal_contDiffAt ((hr z hz).1.of_le (by norm_num)) (hr z hz).2).differentiableAt_one.hasFDerivAt
  have hc : (fun x => ⟪N x,N x⟫) =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
    filter_upwards [e.open_target.mem_nhds hz] with x hx
    rw [real_inner_self_eq_norm_sq,show ‖N x‖ = 1 from euclideanUnitChartNormal_unit (hr x hx).2,one_pow]
  have h := inner_direction_zero_of_constant hN hN hc v
  apply (chartEuclideanTangent_iff_unitNormal (hr z hz).2 _).mpr
  change ⟪fderiv ℝ N z v,N z⟫ = 0
  change ⟪N z,fderiv ℝ N z v⟫+⟪fderiv ℝ N z v,N z⟫ = 0 at h
  rw [real_inner_comm (fderiv ℝ N z v) (N z)] at h
  linarith

/-- The Weingarten identity for the Hessian expression of the original
immersion. No conformality, minimality or principal coordinates are assumed. -/
theorem chart_second_fundamental_weingarten_identity {M : Type*} [TopologicalSpace M]
    {F : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ} (hr : RegularImmersionChart F e)
    {z : ℂ} (hz : z ∈ e.target) (v w : ℂ) :
    chartScalarSecondFundamentalForm (F ∘ e.symm) z v w =
      -⟪fderiv ℝ (euclideanUnitChartNormal (F ∘ e.symm)) z v,coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) z w)⟫ := by
  let Y := F ∘ e.symm
  let N := euclideanUnitChartNormal Y
  let T := fun x => coordinateToEuclidean (fderiv ℝ Y x w)
  let Q := fderiv ℝ (fderiv ℝ Y) z
  let L := coordinateToEuclidean.comp (ContinuousLinearMap.apply ℝ (Fin 3 → ℝ) w)
  have hN := (euclideanUnitChartNormal_contDiffAt ((hr z hz).1.of_le (by norm_num)) (hr z hz).2).differentiableAt_one.hasFDerivAt
  have hT : HasFDerivAt T (L.comp Q) z := L.hasFDerivAt.comp z
    (((hr z hz).1.fderiv_right (m := 1) (by simp)).differentiableAt_one.hasFDerivAt)
  have hc : (fun x => ⟪T x,N x⟫) =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
    filter_upwards [e.open_target.mem_nhds hz] with x hx
    exact (chartEuclideanTangent_iff_unitNormal (hr x hx).2 _).mp ⟨w,rfl⟩
  have h := inner_direction_zero_of_constant hT hN hc v
  change ⟪T z,fderiv ℝ N z v⟫ + ⟪coordinateToEuclidean (Q v w),N z⟫ = 0 at h
  rw [real_inner_comm (fderiv ℝ N z v) (T z)] at h
  change chartScalarSecondFundamentalForm Y z v w = -⟪fderiv ℝ N z v,T z⟫
  unfold chartScalarSecondFundamentalForm
  rw [iteratedFDeriv_two_apply]
  change Q v w ⬝ᵥ unitCrossNormal (fderiv ℝ Y z 1) (fderiv ℝ Y z I) = _
  rw [← euclidean_cartesian_dot,← euclidean_chart_normal_eq_unitCross]
  linarith

/-- The usual pointwise norm bound for the scalar second fundamental form
in the induced metric is equivalent to the corresponding Gauss derivative bound. -/
theorem chart_second_fundamental_bound_iff {M : Type*} [TopologicalSpace M]
    {F : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ} (hr : RegularImmersionChart F e)
    {z : ℂ} (hz : z ∈ e.target) {B : ℝ} (hB : 0 ≤ B) :
    (∀ v w : ℂ, |chartScalarSecondFundamentalForm (F ∘ e.symm) z v w| ≤
      B * ‖coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) z v)‖ * ‖coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) z w)‖) ↔
    (∀ v : ℂ, ‖fderiv ℝ (euclideanUnitChartNormal (F ∘ e.symm)) z v‖ ≤
      B * ‖coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) z v)‖) := by
  let N := euclideanUnitChartNormal (F ∘ e.symm)
  let T := fun v => coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) z v)
  constructor
  · intro h v
    let D := fderiv ℝ N z v
    obtain ⟨w,hw⟩ := euclidean_normal_derivative_is_tangent hr hz v
    change T w = D at hw
    have hs := h v w
    rw [chart_second_fundamental_weingarten_identity hr hz,abs_neg] at hs
    change |⟪D,T w⟫| ≤ B*‖T v‖*‖T w‖ at hs
    rw [hw,real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _),pow_two] at hs
    by_cases h0 : D = 0
    · change ‖D‖ ≤ B*‖T v‖
      rw [h0,norm_zero]
      exact mul_nonneg hB (norm_nonneg _)
    · exact le_of_mul_le_mul_right hs (norm_pos_iff.mpr h0)
  · intro h v w
    rw [chart_second_fundamental_weingarten_identity hr hz,abs_neg]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (h v) (norm_nonneg _))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chart_second_fundamental_bound_iff
