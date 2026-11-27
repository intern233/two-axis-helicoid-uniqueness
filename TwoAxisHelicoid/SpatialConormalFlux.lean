import TwoAxisHelicoid.NullEuclideanMetric
import TwoAxisHelicoid.PiecewiseComplexPeriods

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped RealInnerProductSpace

/-- The right conormal of a parametrized surface curve. Both vectors here
are computed from the Euclidean position derivative in an oriented
conformal chart. At zero velocity the formula gives zero. -/
noncomputable def chartRightUnitConormal (X : ℂ → Fin 3 → ℝ) (z v : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
  ‖D (-I*v)‖⁻¹ • D (-I*v)

private theorem null_tangent_quarter_turn {p : Fin 3 → ℂ} (hp : ComplexNull p) (v : ℂ) :
    let D := coordinateToEuclidean.comp (nullRealDerivative p)
    ‖D (-I*v)‖ = ‖D v‖ ∧ inner ℝ (D v) (D (-I*v)) = 0 := by
  let D := coordinateToEuclidean.comp (nullRealDerivative p)
  have hn (w : ℂ) : ‖D w‖^2 = nullMetric p*‖w‖^2 := nullRealDerivative_euclidean_norm_sq hp w
  have hv : ‖-I*v‖ = ‖v‖ := by simp
  have hs : ‖v+(-I*v)‖^2 = ‖v‖^2+‖-I*v‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.neg_re,Complex.neg_im,I_re,I_im]
    ring
  have h := norm_add_sq_real (D v) (D (-I*v))
  rw [← map_add,hn,hn,hn,hs] at h
  exact ⟨(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [hn,hn,hv]),by linarith⟩

/-- The conormal is tangent to the surface, unit length and orthogonal to
the curve's Euclidean tangent. Its orientation corresponds to turning
clockwise in the complex parameter. -/
theorem chartRightUnitConormal_spec {X : ℂ → Fin 3 → ℝ} {z v : ℂ} {p : Fin 3 → ℂ}
    (hp : ComplexNull p) (hD : HasFDerivAt X (nullRealDerivative p) z)
    (hv : fderiv ℝ (coordinateToEuclidean ∘ X) z v ≠ 0) :
    let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
    let n := chartRightUnitConormal X z v
    ‖n‖ = 1 ∧ inner ℝ (D v) n = 0 ∧ n ∈ Set.range D := by
  let D := coordinateToEuclidean.comp (nullRealDerivative p)
  have hd := (coordinateToEuclidean.hasFDerivAt.comp z hD).fderiv
  obtain ⟨hl,ho⟩ := null_tangent_quarter_turn hp v
  have hne : ‖D (-I*v)‖ ≠ 0 := by rw [hl]; exact norm_ne_zero_iff.mpr (hd ▸ hv)
  simp only [chartRightUnitConormal,hd]
  change ‖‖D (-I*v)‖⁻¹ • D (-I*v)‖ = 1 ∧ inner ℝ (D v) (‖D (-I*v)‖⁻¹ • D (-I*v)) = 0 ∧
    ‖D (-I*v)‖⁻¹ • D (-I*v) ∈ Set.range D
  refine ⟨?_,?_,⟨‖D (-I*v)‖⁻¹ • (-I*v),map_smul D _ _⟩⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hne]
  · rw [real_inner_smul_right,ho,mul_zero]

/-- The geometric conormal times the Euclidean speed equals the imaginary
part of the actual coordinate differential, including stationary points. -/
theorem chartRightUnitConormal_density {X : ℂ → Fin 3 → ℝ} {z : ℂ} {p : Fin 3 → ℂ}
    (hp : ComplexNull p) (hD : HasFDerivAt X (nullRealDerivative p) z) (v : ℂ) (j : Fin 3) :
    ‖fderiv ℝ (coordinateToEuclidean ∘ X) z v‖ * chartRightUnitConormal X z v j = (v*p j).im := by
  let D := coordinateToEuclidean.comp (nullRealDerivative p)
  have hd := (coordinateToEuclidean.hasFDerivAt.comp z hD).fderiv
  have hnorm : ‖D (-I*v)‖ = ‖D v‖ := (null_tangent_quarter_turn hp v).1
  have hvec : ‖D v‖ • (‖D (-I*v)‖⁻¹ • D (-I*v)) = D (-I*v) := by
    rw [← hnorm]
    by_cases h : D (-I*v) = 0
    · simp only [h,smul_zero]
    · rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr h),one_smul]
  change ‖fderiv ℝ (coordinateToEuclidean ∘ X) z v‖ * (‖fderiv ℝ (coordinateToEuclidean ∘ X) z (-I*v)‖⁻¹ •
    fderiv ℝ (coordinateToEuclidean ∘ X) z (-I*v)) j = (v*p j).im
  simp only [hd]
  calc
    _ = D (-I*v) j := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w j) hvec
    _ = (v*p j).im := by change ((-I*v)*p j).re = _; rw [mul_assoc]; simp

noncomputable def ComplexPeriodArc.spatialConormalFlux {Ω : Set ℂ} (a : ComplexPeriodArc Ω)
    (X : ℂ → Fin 3 → ℝ) (j : Fin 3) : ℝ := ∫ s in a.left..a.right,
  ‖fderiv ℝ (coordinateToEuclidean ∘ X) (a.curve s) (a.velocity s)‖ *
    chartRightUnitConormal X (a.curve s) (a.velocity s) j

theorem ComplexPeriodArc.spatialConormalFlux_eq_im {Ω : Set ℂ} (a : ComplexPeriodArc Ω)
    (X : ℂ → Fin 3 → ℝ) (p : ℂ → Fin 3 → ℂ) (hD : ∀ z ∈ Ω, HasFDerivAt X (nullRealDerivative (p z)) z)
    (hnull : ∀ z ∈ Ω, ComplexNull (p z)) (j : Fin 3) (hc : ContinuousOn (fun z => p z j) Ω) :
    a.spatialConormalFlux X j = (a.integral (fun z => p z j)).im := by
  have hi : IntervalIntegrable (fun s => a.velocity s*p (a.curve s) j) volume a.left a.right :=
    (a.continuous_velocity.mul (hc.comp a.continuous_curve a.stays)).intervalIntegrable_of_Icc a.ordered
  have he : (a.integral (fun z => p z j)).im = ∫ s in a.left..a.right, (a.velocity s*p (a.curve s) j).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hi).symm
  rw [he]
  apply intervalIntegral.integral_congr
  intro s hs
  have h := a.stays (by rwa [uIcc_of_le a.ordered] at hs)
  exact chartRightUnitConormal_density (hnull _ h) (hD _ h) (a.velocity s) j

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chartRightUnitConormal_spec
#print axioms TwoAxisHelicoid.ComplexPeriodArc.spatialConormalFlux_eq_im
