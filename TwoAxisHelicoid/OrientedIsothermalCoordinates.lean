import TwoAxisHelicoid.RegularMinimalIsothermal
import Mathlib.Analysis.Complex.Conformal

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1400000

/-- For a real similarity of the complex plane, positive oriented
Jacobian singles out the Cauchy–Riemann equations. -/
theorem positive_plane_similarity_complex_linear (L : ℂ →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 < c) (hg : ∀ v, normSq (L v) = c*normSq v)
    (hori : 0 < (L 1).re*(L I).im-(L 1).im*(L I).re) : L I = I • L 1 := by
  let A := L 1
  let B := L I
  let d := A.re*B.im-A.im*B.re
  have hd : 0 < d := hori
  have ha : A.re*A.re+A.im*A.im = c := by simpa [A,normSq_apply] using hg 1
  have hb : B.re*B.re+B.im*B.im = c := by simpa [B,normSq_apply] using hg I
  have hs := hg (1+I)
  rw [map_add] at hs
  change normSq (A+B) = _ at hs
  simp [normSq_apply] at hs
  have hab : A.re*B.re+A.im*B.im = 0 := by linarith only [ha,hb,hs]
  have hdsq : d^2 = c^2 := by
    change (A.re*B.im-A.im*B.re)^2 = c^2
    calc
      _ = (A.re*A.re+A.im*A.im)*(B.re*B.re+B.im*B.im)-(A.re*B.re+A.im*B.im)^2 := by ring
      _ = _ := by rw [ha,hb,hab]; ring
  have hdc : d = c := by nlinarith only [hdsq,hc,hd]
  have hdc' : A.re*B.im-A.im*B.re = c := hdc
  have hbr : c*(B.re+A.im) = 0 := by
    linear_combination A.re*hab - A.im*hdc' - B.re*ha
  have hbi : c*(B.im-A.re) = 0 := by
    linear_combination A.im*hab + A.re*hdc' - B.im*ha
  have hbr' := (mul_eq_zero.mp hbr).resolve_left hc.ne'
  have hbi' := (mul_eq_zero.mp hbi).resolve_left hc.ne'
  apply Complex.ext
  · change B.re = (I*A).re
    simp
    linarith only [hbr']
  · change B.im = (I*A).im
    simp
    linarith only [hbi']

/-- Two oriented isothermal parametrizations that describe the same
surface have holomorphic transition on their common patch. Orientation
is tested directly with the cross products of their tangent vectors. -/
theorem oriented_isothermal_transition_differentiableAt {X Y : ℂ → Fin 3 → ℝ}
    {f : ℂ → ℂ} {z : ℂ} (h : X =ᶠ[𝓝 z] (Y ∘ f))
    (hY : DifferentiableAt ℝ Y (f z)) (hf : DifferentiableAt ℝ f z)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : ∀ v, fderiv ℝ X z v ⬝ᵥ fderiv ℝ X z v = a*normSq v)
    (hy : ∀ v, fderiv ℝ Y (f z) v ⬝ᵥ fderiv ℝ Y (f z) v = b*normSq v)
    (ho : 0 < ((fderiv ℝ X z 1) ⨯₃ (fderiv ℝ X z I)) ⬝ᵥ
      ((fderiv ℝ Y (f z) 1) ⨯₃ (fderiv ℝ Y (f z) I))) : DifferentiableAt ℂ f z := by
  let L := fderiv ℝ f z
  let D := fderiv ℝ Y (f z)
  have he (v : ℂ) : fderiv ℝ X z v = D (L v) := by
    rw [h.fderiv_eq,fderiv_comp z hY hf]
    rfl
  have hg (v : ℂ) : normSq (L v) = a/b * normSq v := by
    have hy' := hy (L v)
    change D (L v) ⬝ᵥ D (L v) = _ at hy'
    rw [← he,hx] at hy'
    field_simp
    linarith only [hy']
  have hor : 0 < (L 1).re*(L I).im - (L 1).im*(L I).re := by
    rw [he,he,real_linear_complex_expansion D (L 1),real_linear_complex_expansion D (L I),
      cross_product_two_basis_changes,smul_dotProduct,smul_eq_mul] at ho
    let N := (D 1) ⨯₃ (D I)
    change 0 < _ * (N ⬝ᵥ N) at ho
    exact pos_of_mul_pos_left ho (Finset.sum_nonneg fun i _ => mul_self_nonneg (N i))
  exact differentiableAt_complex_iff_differentiableAt_real.mpr
    ⟨hf,positive_plane_similarity_complex_linear L (div_pos ha hb) hg hor⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_isothermal_transition_differentiableAt
