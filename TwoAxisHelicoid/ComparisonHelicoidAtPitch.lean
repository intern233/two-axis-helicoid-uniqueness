import TwoAxisHelicoid.ComparisonHelicoidConformalCoordinates
import TwoAxisHelicoid.ReferenceFrameHarmonic

namespace TwoAxisHelicoid
open Complex Set Function InnerProductSpace
open scoped ComplexConjugate ContDiff Topology

/-- The physical ruling and height corresponding to a conformal parameter
on a comparison helicoid of signed angular speed α. -/
noncomputable def helicoidRulingParameter (α b : ℝ) (z : ℂ) : ℂ :=
  ⟨α⁻¹*Real.sinh z.re,b+α⁻¹*z.im⟩

noncomputable def conformalComparisonHelicoid (g : ℂ) (α b : ℝ) : ℂ → Fin 3 → ℝ :=
  axisRuledHelicoid g α b ∘ helicoidRulingParameter α b

private theorem comparison_rotation {g : ℂ} (hg : normSq g=1) : ‖conj (-I*g)‖=1 := by
  have h := Complex.normSq_eq_norm_sq g
  rw [hg] at h
  have unit : ‖g‖=1 := by nlinarith [norm_nonneg g]
  simp [unit]

private theorem conformalComparisonHelicoid_coordinates {g : ℂ} (hg : normSq g=1)
    {α : ℝ} (ha : α≠0) (b : ℝ) :
    conformalComparisonHelicoid g α b =
      lineAxisCoordinates (conj (-I*g)) (comparison_rotation hg) ![0,0,-b] ∘
      (fun z => α⁻¹ • comparisonHelicoidSheet z) := by
  funext z
  have angle : α*(b+α⁻¹*z.im-b)=z.im := by field_simp; ring
  have phase : I*(α*(b+α⁻¹*z.im-b):ℝ)=(z.im:ℂ)*I := by rw [angle,mul_comm]
  change axisRuledHelicoid g α b ⟨α⁻¹*Real.sinh z.re,b+α⁻¹*z.im⟩ =
    verticalRotation (conj (conj (-I*g))) (α⁻¹ • comparisonHelicoidSheet z-![0,0,-b])
  rw [starRingEnd_self_apply,comparisonHelicoidSheet_coordinates]
  funext j
  fin_cases j
  · change α⁻¹*Real.sinh z.re*(g*Complex.exp (I*(α*(b+α⁻¹*z.im-b):ℝ))).im =
      (-I*g).re*(α⁻¹*(Real.sinh z.re*Real.cos z.im)-0)-(-I*g).im*(α⁻¹*(Real.sinh z.re*Real.sin z.im)-0)
    rw [phase]
    simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    ring
  · change -(α⁻¹*Real.sinh z.re)*(g*Complex.exp (I*(α*(b+α⁻¹*z.im-b):ℝ))).re =
      (-I*g).im*(α⁻¹*(Real.sinh z.re*Real.cos z.im)-0)+(-I*g).re*(α⁻¹*(Real.sinh z.re*Real.sin z.im)-0)
    rw [phase]
    simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    ring
  · change b+α⁻¹*z.im=α⁻¹*z.im- -b
    ring

/-- The ruled comparison surface has a harmonic conformal regular chart at
every point, for arbitrary initial Gauss phase, height, and signed pitch. -/
theorem conformalComparisonHelicoid_regular {g : ℂ} (hg : normSq g=1)
    {α : ℝ} (ha : α≠0) (b : ℝ) (z : ℂ) :
    (∀ j, HarmonicAt (fun w => conformalComparisonHelicoid g α b w j) z) ∧
    ConformalCoordinateDerivatives (conformalComparisonHelicoid g α b) z ∧
    Injective (fderiv ℝ (conformalComparisonHelicoid g α b) z) := by
  obtain ⟨h,c,i⟩ := comparisonHelicoidSheet_regular z
  obtain ⟨h',c',i'⟩ := scalar_harmonic_conformal_chart h c i (inv_ne_zero ha)
  rw [conformalComparisonHelicoid_coordinates hg ha]
  exact lineAxisCoordinates_harmonic_chart _ (comparison_rotation hg) _ h' c' i'

theorem helicoidRulingParameter_at_axis {α : ℝ} (ha : α≠0) (b h : ℝ) :
    helicoidRulingParameter α b (I*(α*(h-b):ℝ))=I*h := by
  apply Complex.ext
  · simp [helicoidRulingParameter]
  · simp [helicoidRulingParameter,← mul_assoc,ha]

/-- At a given physical axis point the actual ruled and conformal
parametrizations have the same tangent plane. -/
theorem conformalComparisonHelicoid_axis_tangent {g : ℂ} (hg : normSq g=1)
    {α : ℝ} (ha : α≠0) (b h : ℝ) :
    range (fderiv ℝ (conformalComparisonHelicoid g α b) (I*(α*(h-b):ℝ))) =
      range (fderiv ℝ (axisRuledHelicoid g α b) (I*h)) := by
  let v := I*(α*(h-b):ℝ)
  let φ := helicoidRulingParameter α b
  have dv : DifferentiableAt ℝ φ v := by
    change DifferentiableAt ℝ (fun z : ℂ => Complex.equivRealProdCLM.symm
      (α⁻¹*Real.sinh z.re,b+α⁻¹*z.im)) v
    fun_prop
  have dr : DifferentiableAt ℝ (axisRuledHelicoid g α b) (φ v) := by
    apply differentiableAt_pi.mpr
    intro j
    fin_cases j <;> unfold axisRuledHelicoid <;> dsimp <;> fun_prop
  have derivative : fderiv ℝ (conformalComparisonHelicoid g α b) v=
      (fderiv ℝ (axisRuledHelicoid g α b) (φ v)).comp (fderiv ℝ φ v) :=
    fderiv_comp v dr dv
  have inj := (conformalComparisonHelicoid_regular hg ha b v).2.2
  have injφ : Injective (fderiv ℝ φ v) := by
    intro u w eq
    apply inj
    rw [derivative]
    exact congrArg (fderiv ℝ (axisRuledHelicoid g α b) (φ v)) eq
  have surj := (LinearMap.injective_iff_surjective (f:=(fderiv ℝ φ v).toLinearMap)).mp injφ
  change range (fderiv ℝ (conformalComparisonHelicoid g α b) v)=_
  rw [derivative]
  have point : φ v=I*h := helicoidRulingParameter_at_axis ha b h
  rw [point]
  exact surj.range_comp _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformalComparisonHelicoid_regular
#print axioms TwoAxisHelicoid.conformalComparisonHelicoid_axis_tangent
