import TwoAxisHelicoid.MinimalDiskHorizontalPrimitive
import TwoAxisHelicoid.LocalFiniteGaussDevelopment
import TwoAxisHelicoid.QuantitativePlaneInverse

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology ContDiff

private theorem finite_gauss_normal_differentiable (g : ℂ) :
    DifferentiableAt ℝ (coordinateToEuclidean ∘ finiteGaussNormal) g := by
  apply coordinateToEuclidean.differentiableAt.comp
  apply differentiableAt_pi.mpr
  intro j
  have den : 1+normSq g≠0 := (by linarith [normSq_nonneg g] : 0<1+normSq g).ne'
  have d : DifferentiableAt ℝ (fun h : ℂ => 1+normSq h) g := by
    change DifferentiableAt ℝ (fun h : ℂ => 1+(h.re*h.re+h.im*h.im)) g
    fun_prop
  have dinv := (hasDerivAt_inv den).differentiableAt.comp g d
  fin_cases j
  · change DifferentiableAt ℝ (fun h : ℂ => 2*h.re/(1+normSq h)) g
    simp only [div_eq_mul_inv]
    exact (reCLM.differentiableAt.const_mul 2).mul dinv
  · change DifferentiableAt ℝ (fun h : ℂ => 2*h.im/(1+normSq h)) g
    simp only [div_eq_mul_inv]
    exact (imCLM.differentiableAt.const_mul 2).mul dinv
  · change DifferentiableAt ℝ (fun h : ℂ => (normSq h-1)/(1+normSq h)) g
    have num : DifferentiableAt ℝ (fun h : ℂ => normSq h-1) g := by
      change DifferentiableAt ℝ (fun h : ℂ => h.re*h.re+h.im*h.im-1) g
      fun_prop
    simp only [div_eq_mul_inv]
    exact num.mul dinv

/-- Curvature estimate in a genuine disk of a smooth regular minimal
parametrization. Both the lower speed bound and the separation of the
actual oriented normal from the north pole are measured in the given
physical coordinates. No conformal radius is assumed. -/
theorem regular_minimal_disk_bounded_normal_derivative {X : ℂ → Fin 3 → ℝ} {a : ℂ} {R D r : ℝ}
    (Rp : 0<R) (dp : 0≤D) (rp : 0<r) (room : (37/2*D)*r<R/2)
    (data : ∀ z∈ball a R, ContDiffAt ℝ ∞ X z ∧ Function.Injective (fderiv ℝ X z) ∧ coordinateMeanCurvature X z=0)
    (bound : ∀ z∈ball a R, unitCrossNormal (fderiv ℝ X z 1) (fderiv ℝ X z I) 2≤15/16)
    (lower : ∀ z∈ball a R, ∀ v, ‖v‖≤D*‖coordinateToEuclidean (fderiv ℝ X z v)‖) (v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal X) a v‖≤(48/r)*‖coordinateToEuclidean (fderiv ℝ X a v)‖ := by
  classical
  let G := measuredChartGauss X
  let form := physicalHorizontalForm X
  have near (z : ℂ) (hz : z∈ball a R) : ∀ᶠ w in 𝓝 z,
      ContDiffAt ℝ ∞ X w ∧ Function.Injective (fderiv ℝ X w) ∧ coordinateMeanCurvature X w=0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact data w hw
  have loc (z : ℂ) (hz : z∈ball a R) := minimal_chart_local_horizontal_development (near z hz) (bound z hz)
  obtain ⟨F,sF,dF⟩ := primitive_on_ball_of_local_c2 (fun z hz => (loc z hz).1)
  let q := fun z => if hz : z∈ball a R then Classical.choose (loc z hz).2.1 else 0
  have dG (z : ℂ) (hz : z∈ball a R) : HasFDerivAt G ((complexScaleReal (q z)).comp (form z)) z := by
    simpa only [q,dite_eq_left hz] using Classical.choose_spec (loc z hz).2.1
  have bG (z : ℂ) (hz : z∈ball a R) : ‖G z‖≤6 := (loc z hz).2.2.1
  have bF (z : ℂ) (hz : z∈ball a R) (w : ℂ) : ‖w‖≤(37/2*D)*‖fderiv ℝ F z w‖ := by
    rw [(dF z hz).fderiv]
    have h := lower z hz w
    rw [(loc z hz).2.2.2.2 w] at h
    have sq : normSq (G z)≤36 := by
      rw [Complex.normSq_eq_norm_sq]
      have power := ((sq_le_sq₀ (norm_nonneg (G z)) (by norm_num : (0:ℝ)≤6)).mpr (bG z hz))
      norm_num at power
      exact power
    calc
      _ ≤ D*((1+normSq (G z))/2*‖form z w‖) := h
      _ = (1+normSq (G z))/2*(D*‖form z w‖) := by ring
      _ ≤ 37/2*(D*‖form z w‖) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg dp (norm_nonneg _))
      _ = _ := by ring
  have cb := quantitative_developed_cauchy_estimate (F:=F) (G:=G) (q:=q) Rp (by positivity) rp room sF bF
    (fun z hz => (dF z hz).fderiv.symm ▸ dG z hz) bG
  have qa : ‖q a‖≤12/r := by convert cb using 1; norm_num
  let S := coordinateToEuclidean ∘ finiteGaussNormal
  have ha := mem_ball_self Rp (x:=a)
  have diff := (finite_gauss_normal_differentiable (G a)).hasFDerivAt.comp a (dG a ha)
  have normal := diff.congr_of_eventuallyEq ((loc a ha).2.2.2.1)
  rw [normal.fderiv]
  change ‖(fderiv ℝ S (G a)) (form a v*q a)‖≤_
  have A : ‖fderiv ℝ S (G a)‖≤(2:ℝ) := norm_fderiv_le_of_lipschitz ℝ finite_gauss_normal_lipschitz
  have hform : ‖form a v‖≤2*‖coordinateToEuclidean (fderiv ℝ X a v)‖ := by
    rw [(loc a ha).2.2.2.2 v]
    nlinarith [mul_nonneg (normSq_nonneg (G a)) (norm_nonneg (form a v))]
  calc
    _ ≤ ‖fderiv ℝ S (G a)‖*‖form a v*q a‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2*‖form a v*q a‖ := mul_le_mul_of_nonneg_right A (norm_nonneg _)
    _ = 2*(‖form a v‖*‖q a‖) := by rw [norm_mul]
    _ ≤ 2*((2*‖coordinateToEuclidean (fderiv ℝ X a v)‖)*(12/r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hform qa (norm_nonneg _) (by positivity)) (by norm_num)
    _ = _ := by ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_minimal_disk_bounded_normal_derivative
