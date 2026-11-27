import TwoAxisHelicoid.PlaneHarmonicCoordinateConjugate

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff

/-- Strict positivity of the dual metric quadratic form at a covector
whose first component is nonzero. -/
theorem plane_metric_dual_numerator_pos {E F G p q : ℝ} (he : 0<E)
    (hd : F^2<E*G) (hp : p≠0) : 0<G*p^2-2*F*p*q+E*q^2 := by
  have guard : 0<(E*G-F^2)*p^2 := mul_pos (sub_pos.mpr hd) (sq_pos_of_ne_zero hp)
  have h : E*(G*p^2-2*F*p*q+E*q^2)=(F*p-E*q)^2+(E*G-F^2)*p^2 := by ring
  exact pos_of_mul_pos_right (h.symm ▸ add_pos_of_nonneg_of_pos (sq_nonneg _) guard) he.le

/-- In a positive plane metric, a covector and its metric rotation are
an orthogonal equal-length coframe for the dual metric. -/
theorem plane_metric_conjugate_coframe {E F G W p q : ℝ} (hw : 0<W)
    (hsq : W^2=E*G-F^2) (hn : G*p^2-2*F*p*q+E*q^2 ≠ 0) (x y : ℝ) :
    E*x^2+2*F*x*y+G*y^2=
      (W^2/(G*p^2-2*F*p*q+E*q^2))*
      ((p*x+q*y)^2+((F*p-E*q)/W*x+(G*p-F*q)/W*y)^2) := by
  let H := G*p^2-2*F*p*q+E*q^2
  let k := (F*p-E*q)*x+(G*p-F*q)*y
  have kg : (F*p-E*q)/W*x+(G*p-F*q)/W*y=k/W := by dsimp [k]; ring
  rw [kg]
  calc
    _ = (W^2*(p*x+q*y)^2+k^2)/H := by
      apply (eq_div_iff (show H≠0 from hn)).mpr
      dsimp [k,H]
      rw [hsq]
      ring
    _ = _ := by dsimp [H]; field_simp [hw.ne',hn]

/-- A real-linear plane map is an isomorphism when its two coordinate
functionals have nonzero determinant. -/
theorem plane_coframe_bijective (T : ℂ →L[ℝ] ℂ) (p q a b : ℝ)
    (coordinates : ∀ v : ℂ, T v=⟨p*v.re+q*v.im,a*v.re+b*v.im⟩) (det : p*b-q*a≠0) :
    Function.Bijective T := by
  constructor
  · intro z w h
    rw [coordinates,coordinates] at h
    have x := congrArg Complex.re h
    have y := congrArg Complex.im h
    dsimp only at x y
    apply Complex.ext
    · have h₁ : (p*b-q*a)*(z.re-w.re)=0 := by linear_combination b*x-q*y
      exact sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left det)
    · have h₂ : (p*b-q*a)*(z.im-w.im)=0 := by linear_combination p*y-a*x
      exact sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left det)
  · intro z
    let d := p*b-q*a
    have nd : d≠0 := det
    refine ⟨⟨(b*z.re-q*z.im)/d,(p*z.im-a*z.re)/d⟩,?_⟩
    rw [coordinates]
    apply Complex.ext
    · change p*((b*z.re-q*z.im)/d)+q*((p*z.im-a*z.re)/d)=z.re
      calc
        _ = d*z.re/d := by dsimp [d]; ring
        _ = z.re := by field_simp [nd]
    · change a*((b*z.re-q*z.im)/d)+b*((p*z.im-a*z.re)/d)=z.im
      calc
        _ = d*z.im/d := by dsimp [d]; ring
        _ = z.im := by field_simp [nd]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_metric_conjugate_coframe
#print axioms TwoAxisHelicoid.plane_coframe_bijective

