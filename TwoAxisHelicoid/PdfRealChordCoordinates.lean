import TwoAxisHelicoid.JacobiChordKernel

namespace TwoAxisHelicoid
open Complex

/-- Real coordinates of the forward and reciprocal chord variables.
The factor (1-s)(1+s) avoids interval cancellation at either endpoint. -/
theorem real_chord_coordinates {h k : ℝ} (circle : h^2+k^2=1) (s : ℝ) :
    let u : ℂ := ⟨h,k*s⟩
    let n := -(k^2*(1-s)*(1+s))
    let d := h^2+(k*s-1)^2
    let b := h^2+(k*s+1)^2
    jacobiChordX u=⟨n/d,(2*h)/d⟩ ∧ (jacobiChordX u)⁻¹=⟨n/b,(-2*h)/b⟩ := by
  dsimp only
  have num : h*h+(k*s+1)*(k*s-1)= -(k^2*(1-s)*(1+s)) := by nlinarith only [circle]
  have imag : (k*s+1)*h-h*(k*s-1)=2*h := by ring
  have imag' : (k*s-1)*h-h*(k*s+1)= -2*h := by ring
  have rev : h*h+(k*s-1)*(k*s+1)= -(k^2*(1-s)*(1+s)) := by nlinarith only [circle]
  constructor
  · apply Complex.ext
    · simp only [jacobiChordX,Complex.div_re,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← add_div,num,pow_two]
    · simp only [jacobiChordX,Complex.div_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← sub_div,imag,pow_two]
  · apply Complex.ext
    · simp only [jacobiChordX,inv_div,Complex.div_re,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← add_div,rev,pow_two]
    · simp only [jacobiChordX,inv_div,Complex.div_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
        I_re,I_im,add_zero,sub_zero,Complex.normSq_apply,← sub_div,imag',pow_two]

theorem real_chord_product_region {t : ℝ} (ht : 0<t) (hu : t≤7/5) (s : ℝ) :
    let x := jacobiChordX (jacobiChordPoint t (s:ℂ))
    x≠0 ∧ ‖jacobiNome (1/t)‖*‖x‖<1 ∧ ‖jacobiNome (1/t)‖*‖x⁻¹‖<1 := by
  let u := jacobiChordPoint t (s:ℂ)
  have re : u.re=leftChordH (leftNome t) := by simp [u,jacobiChordPoint]
  have hh := leftChordH_pos (leftNome_pos t)
  have pos : 0<u.re := re ▸ hh
  have bounds := jacobiChordX_norm_bounds hh (show leftChordH (leftNome t)/2<u.re by rw [re];linarith)
  have strict := jacobiChord_nome_bound (leftNome_pos t) (leftNome_lt_one_third ht hu).le
  have nome : ‖jacobiNome (1/t)‖=(leftNome t)^2 := by
    rw [jacobiNome_inverse_eq_leftNome ht]
    simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_sq]
  dsimp only
  rw [nome]
  exact ⟨jacobiChordX_ne_zero pos,
    (mul_le_mul_of_nonneg_left bounds.1 (sq_nonneg _)).trans_lt strict,
    (mul_le_mul_of_nonneg_left bounds.2 (sq_nonneg _)).trans_lt strict⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.real_chord_coordinates
#print axioms TwoAxisHelicoid.real_chord_product_region

