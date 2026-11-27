import TwoAxisHelicoid.AxisHelicoidCalibration
import TwoAxisHelicoid.AxisSpatialNormalization

namespace TwoAxisHelicoid
open Complex Set

theorem axisRuledHelicoid_ruling (α b r v : ℝ) :
    axisRuledHelicoid I α b ⟨r,v⟩ = ![r*Real.cos (α*(v-b)),r*Real.sin (α*(v-b)),v] := by
  let θ := α*(v-b)
  have he : I*(θ : ℂ) = (θ : ℂ)*I := mul_comm _ _
  funext j
  fin_cases j
  · change r*(I*Complex.exp (I*(θ : ℂ))).im = r*Real.cos θ
    rw [he,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.exp_ofReal_mul_I_re]
  · change -r*(I*Complex.exp (I*(θ : ℂ))).re = r*Real.sin θ
    rw [he,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,neg_mul_neg,Complex.exp_ofReal_mul_I_im]
  · rfl

theorem axisRuledHelicoid_standard_ruling (α : ℝ) (w : ℂ) :
    axisRuledHelicoid I α 0 w =
      ![w.re*Real.cos (α*w.im),w.re*Real.sin (α*w.im),w.im] := by
  simpa only [sub_zero] using axisRuledHelicoid_ruling α 0 w.re w.im

/-- Height translations and arbitrary starting horizontal rotations do
not change the comparison surface after its pitch is fixed and the
horizontal unit point lies on that surface. -/
theorem axisRuledHelicoid_range_of_horizontal_unit {g : ℂ} (hg : normSq g = 1) (α b : ℝ)
    (hunit : (![1,0,0] : Fin 3 → ℝ) ∈ range (axisRuledHelicoid g α b)) :
    range (axisRuledHelicoid g α b) = range (axisRuledHelicoid I α 0) := by
  let q := g*Complex.exp (I*(α*(0-b) : ℝ))
  have hr : q.re = 0 := by
    have he := (axisHelicoidSide_eq_zero_iff hg α b _).mpr hunit
    change q.re * 1 + q.im * 0 = 0 at he
    simpa only [mul_one,mul_zero,add_zero] using he
  have hu : normSq q = 1 := by
    dsimp only [q]
    rw [normSq_mul,hg,one_mul,normSq_eq_norm_sq,mul_comm I,Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hn : q.im ≠ 0 := by
    intro h
    change q.re*q.re+q.im*q.im=1 at hu
    rw [hr,h] at hu
    norm_num at hu
  ext P
  rw [← axisHelicoidSide_eq_zero_iff hg,← axisHelicoidSide_eq_zero_iff (by simp : normSq I=1)]
  let e := Complex.exp (I*(α*(P 2-0) : ℝ))
  have he : g*Complex.exp (I*(α*(P 2-b) : ℝ)) = q*e := by
    dsimp [q,e]
    rw [mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hside : axisHelicoidSide g α b P = q.im * axisHelicoidSide I α 0 P := by
    change (g*Complex.exp (I*(α*(P 2-b) : ℝ))).re*P 0+(g*Complex.exp (I*(α*(P 2-b) : ℝ))).im*P 1 =
      q.im*((I*e).re*P 0+(I*e).im*P 1)
    rw [he]
    simp only [Complex.mul_re,Complex.mul_im,hr,zero_mul,zero_sub,zero_add,Complex.I_re,Complex.I_im,one_mul]
    ring
  rw [hside,mul_eq_zero]
  exact or_iff_right hn

/-- In the physical normalization supplied by the analytic end theorem,
the inverse image of the usual pitch-one helicoid is a ruled vertical
helicoid with the original pitch, for every possible height shift. -/
theorem inverse_image_standardHelicoid_axisNormalization {α : ℝ} (hα : α ≠ 0) (b : ℝ) :
    (axisSpatialNormalization hα ![0,0,b]) ⁻¹' (range (fun w : ℂ => standardHelicoid w.re w.im)) =
      range (axisRuledHelicoid I α b) := by
  have hform (P : Fin 3 → ℝ) :
      axisSpatialNormalization hα ![0,0,b] P = ![-α*P 0,-α*P 1,α*(P 2-b)] := by
    rw [axisSpatialNormalization_apply]
    funext j
    fin_cases j <;> simp [verticalRotation_apply]
  ext P
  constructor
  · rintro ⟨w,hw⟩
    rw [hform] at hw
    have hheight := congrFun hw 2
    change w.im = α*(P 2-b) at hheight
    refine ⟨⟨-w.re/α,P 2⟩,?_⟩
    rw [axisRuledHelicoid_ruling,← hheight]
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    change w.re*Real.cos w.im = -α*P 0 at h0
    change w.re*Real.sin w.im = -α*P 1 at h1
    funext j
    fin_cases j
    · change -w.re/α*Real.cos w.im = P 0
      field_simp
      linarith
    · change -w.re/α*Real.sin w.im = P 1
      field_simp
      linarith
    · rfl
  · rintro ⟨⟨r,h⟩,rfl⟩
    refine ⟨⟨-α*r,α*(h-b)⟩,?_⟩
    rw [axisRuledHelicoid_ruling,hform]
    funext j
    fin_cases j <;> simp [standardHelicoid] <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.inverse_image_standardHelicoid_axisNormalization
#print axioms TwoAxisHelicoid.axisRuledHelicoid_range_of_horizontal_unit
