import TwoAxisHelicoid.HorizontalGraphScrewPlacement
import TwoAxisHelicoid.MarkedTorusAngularEscape
import TwoAxisHelicoid.AxisHelicoidGauge

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The horizontal rotation and vertical translation that send the
ruling at physical height h to the real horizontal axis. -/
noncomputable def referenceRulingFrame (α h : ℝ) : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) :=
  lineAxisCoordinates (Complex.exp (((α*h:ℝ):ℂ)*I)) (by simp [Complex.norm_exp]) ![0,0,h]

theorem referenceRulingFrame_apply (α h : ℝ) (p : Fin 3 → ℝ) :
    referenceRulingFrame α h p=
      ![Real.cos (α*h)*p 0+Real.sin (α*h)*p 1,
        -(Real.sin (α*h))*p 0+Real.cos (α*h)*p 1,p 2-h] := by
  let θ := α*h
  ext j
  fin_cases j
  · change (conj (Complex.exp ((θ:ℂ)*I))).re*(p 0-0)-(conj (Complex.exp ((θ:ℂ)*I))).im*(p 1-0)=_
    simp only [Complex.conj_re,Complex.conj_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    simp [θ]
  · change (conj (Complex.exp ((θ:ℂ)*I))).im*(p 0-0)+(conj (Complex.exp ((θ:ℂ)*I))).re*(p 1-0)=_
    simp only [Complex.conj_re,Complex.conj_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    simp [θ]
  · rfl

theorem referenceRulingFrame_ruling (α h r : ℝ) :
    referenceRulingFrame α h (axisRuledHelicoid I α 0 ⟨r,h⟩)=![r,0,0] := by
  rw [referenceRulingFrame_apply,axisRuledHelicoid_standard_ruling]
  ext j
  fin_cases j
  · change Real.cos (α*h)*(r*Real.cos (α*h))+Real.sin (α*h)*(r*Real.sin (α*h))=r
    linear_combination r*(Real.sin_sq_add_cos_sq (α*h))
  · change -(Real.sin (α*h))*(r*Real.cos (α*h))+Real.cos (α*h)*(r*Real.sin (α*h))=0
    ring
  · exact sub_self h

theorem referenceRulingFrame_vertical (α h r : ℝ) :
    referenceRulingFrame α h ![0,0,r]=![0,0,r-h] := by rw [referenceRulingFrame_apply]; simp

private theorem standard_side_coordinates (α : ℝ) (p : Fin 3 → ℝ) :
    axisHelicoidSide I α 0 p= -(Real.sin (α*p 2))*p 0+Real.cos (α*p 2)*p 1 := by
  let θ := α*p 2
  simp only [axisHelicoidSide,sub_zero]
  change (I*Complex.exp (I*(θ:ℂ))).re*p 0+(I*Complex.exp (I*(θ:ℂ))).im*p 1=_
  rw [show I*(θ:ℂ)=(θ:ℂ)*I from mul_comm _ _,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  dsimp only [θ]
  ring

/-- This screw preserves the signed side function, so also the actual
comparison helicoid and each of its two complementary sides. -/
theorem referenceRulingFrame_side (α h : ℝ) (p : Fin 3 → ℝ) :
    axisHelicoidSide I α 0 (referenceRulingFrame α h p)=axisHelicoidSide I α 0 p := by
  rw [standard_side_coordinates,standard_side_coordinates,referenceRulingFrame_apply]
  change -(Real.sin (α*(p 2-h)))*(Real.cos (α*h)*p 0+Real.sin (α*h)*p 1)+
    Real.cos (α*(p 2-h))*(-(Real.sin (α*h))*p 0+Real.cos (α*h)*p 1)=_
  rw [mul_sub,Real.sin_sub,Real.cos_sub]
  linear_combination (-(Real.sin (α*p 2))*p 0+Real.cos (α*p 2)*p 1)*(Real.sin_sq_add_cos_sq (α*h))

theorem referenceRulingFrame_mem_helicoid (α h : ℝ) (p : Fin 3 → ℝ) :
    referenceRulingFrame α h p∈range (axisRuledHelicoid I α 0) ↔ p∈range (axisRuledHelicoid I α 0) := by
  rw [← axisHelicoidSide_eq_zero_iff (by simp : normSq I=1),
    ← axisHelicoidSide_eq_zero_iff (by simp : normSq I=1),referenceRulingFrame_side]

theorem referenceRulingFrame_half_turn (α h : ℝ) (p : Fin 3 → ℝ) :
    referenceRulingFrame α h ![-p 0,-p 1,p 2]=
      ![-(referenceRulingFrame α h p) 0,-(referenceRulingFrame α h p) 1,(referenceRulingFrame α h p) 2] := by
  rw [referenceRulingFrame_apply,referenceRulingFrame_apply]
  ext j
  fin_cases j <;> simp <;> ring

/-- In unit-pitch end coordinates this is exactly the standard
helicoid screw, including the vertical component and its sign. -/
theorem referenceRulingFrame_normalized {α : ℝ} (ha : α≠0) (h : ℝ) (p : Fin 3 → ℝ) :
    coordinateToTube (axisSpatialNormalization ha ![0,0,0] (referenceRulingFrame α h p))=
      helicoidScrewMove (-(α*h)) (coordinateToTube (axisSpatialNormalization ha ![0,0,0] p)) := by
  rw [axis_normalized_tube_vector,axis_normalized_tube_vector,referenceRulingFrame_apply]
  ext <;> simp [helicoidScrewMove] <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.referenceRulingFrame_side
#print axioms TwoAxisHelicoid.referenceRulingFrame_normalized
