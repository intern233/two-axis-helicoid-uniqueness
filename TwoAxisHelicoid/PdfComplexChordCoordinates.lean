import TwoAxisHelicoid.PdfRealChordCoordinates
import TwoAxisHelicoid.PdfAdaptiveChordCell

namespace TwoAxisHelicoid
open Complex

/-- Real and reciprocal coordinates of the chord map at complex arguments,
with a common numerator in a form suitable at the two real endpoints. -/
theorem complex_chord_coordinates {h k : ℝ} (circle : h^2+k^2=1) (s v : ℝ) :
    let dx := k*v
    let r := h-dx
    let y := k*s
    let u : ℂ := ⟨r,y⟩
    let n := -(k^2*(1-s)*(1+s))+dx^2-2*h*dx
    let d := r^2+(y-1)^2
    let b := r^2+(y+1)^2
    jacobiChordX u=⟨n/d,(2*r)/d⟩ ∧ (jacobiChordX u)⁻¹=⟨n/b,(-2*r)/b⟩ := by
  dsimp only
  have f : (h-k*v)*(h-k*v)+(k*s+1)*(k*s-1)=
      -(k^2*(1-s)*(1+s))+(k*v)^2-2*h*(k*v) := by nlinarith only [circle]
  have rev : (h-k*v)*(h-k*v)+(k*s-1)*(k*s+1)=
      -(k^2*(1-s)*(1+s))+(k*v)^2-2*h*(k*v) := by nlinarith only [circle]
  have g : (k*s+1)*(h-k*v)-(h-k*v)*(k*s-1)=2*(h-k*v) := by ring
  have gr : (k*s-1)*(h-k*v)-(h-k*v)*(k*s+1)= -2*(h-k*v) := by ring
  constructor
  · apply Complex.ext
    · simp only [jacobiChordX,Complex.div_re,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← add_div,f,pow_two]
    · simp only [jacobiChordX,Complex.div_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← sub_div,g,pow_two]
  · apply Complex.ext
    · simp only [jacobiChordX,inv_div,Complex.div_re,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← add_div,rev,pow_two]
    · simp only [jacobiChordX,inv_div,Complex.div_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← sub_div,gr,pow_two]

theorem complex_chord_point_coordinates (t : ℝ) (z : ℂ) :
    jacobiChordPoint t z=
      ⟨leftChordH (leftNome t)-leftChordK (leftNome t)*z.im,leftChordK (leftNome t)*z.re⟩ := by
  apply Complex.ext <;> simp [jacobiChordPoint,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_chord_coordinates

