import TwoAxisHelicoid.LambertGeometricRearrangement
import TwoAxisHelicoid.JacobiVerticalIdentity

namespace TwoAxisHelicoid

noncomputable def dualVerticalLambertTerm (q E : ℝ) (j : ℕ) : ℝ :=
  (-1:ℝ)^(j+2)*((j+1:ℕ):ℝ)*q^j*
    (E^(j+1)+q^(2*(j+1))*(E⁻¹)^(j+1))/(1-(-q^2)^(j+1))

noncomputable def manuscriptDualVertical (q E : ℝ) : ℝ :=
  -(E⁻¹)/(1-q/E)^2+∑' j : ℕ, dualVerticalLambertTerm q E j

theorem dual_vertical_term_rescaled {q E : ℝ} (j : ℕ) :
    -(q*dualVerticalLambertTerm q E j)=
      ((j+1:ℕ):ℝ)*(-q*E)^(j+1)/(1-(-q^2)^(j+1))+
      ((j+1:ℕ):ℝ)*(-q^3/E)^(j+1)/(1-(-q^2)^(j+1)) := by
  have a : (-q*E)^(j+1)=(-1:ℝ)^(j+1)*q^(j+1)*E^(j+1) := by rw [← mul_pow,← mul_pow];congr 1;ring
  have b : (-q^3/E)^(j+1)=(-1:ℝ)^(j+1)*(q^(j+1))^3*(E⁻¹)^(j+1) := by
    rw [← pow_mul,div_eq_mul_inv,show -q^3=(-1:ℝ)*q^3 by ring,mul_pow,mul_pow,← pow_mul,Nat.mul_comm 3 (j+1)]
  rw [a,b]
  simp only [dualVerticalLambertTerm,div_eq_mul_inv,pow_mul,pow_succ]
  ring

/-- Algebraic and analytic rearrangement of the two convergent
Jacobi series into the exact signed D series of the attachment. -/
theorem jacobiRealE_eq_manuscript_D {q E : ℝ} (hq : 0<q) (h1 : q<1) (hp : 0<E)
    (up : q*E<1) (down : q^3/E<1) :
    Summable (dualVerticalLambertTerm q E) ∧
      jacobiRealE (-q^2) (q/E)= -q*manuscriptDualVertical q E := by
  let Q := -q^2
  let L := fun (x : ℝ) (n : ℕ) => ((n+1:ℕ):ℝ)*x^(n+1)/(1-Q^(n+1))
  have hQ : ‖Q‖<1 := by change |-q^2|<1;rw [abs_neg,abs_sq];nlinarith [mul_pos hq (sub_pos.mpr h1)]
  have up' : ‖-q*E‖<1 := by change |-q*E|<1;rw [neg_mul,abs_neg,abs_of_pos (mul_pos hq hp)];exact up
  have down' : ‖-q^3/E‖<1 := by change |-q^3/E|<1;rw [neg_div,abs_neg,abs_of_pos (by positivity : 0<q^3/E)];exact down
  obtain ⟨su,eu⟩ := (geometric_lambert_orders_zero_one hQ up').2
  obtain ⟨sd,ed⟩ := (geometric_lambert_orders_zero_one hQ down').2
  change jacobiGeometricSeries Q (-q*E)=∑' n, L (-q*E) n at eu
  change jacobiGeometricSeries Q (-q^3/E)=∑' n, L (-q^3/E) n at ed
  have scale (n : ℕ) : dualVerticalLambertTerm q E n=(-q)⁻¹*(L (-q*E) n+L (-q^3/E) n) := by
    rw [← show -(q*dualVerticalLambertTerm q E n)=L (-q*E) n+L (-q^3/E) n from dual_vertical_term_rescaled n]
    field_simp [hq.ne']
  have F : Summable (L (-q*E)) := su
  have G : Summable (L (-q^3/E)) := sd
  refine ⟨((F.add G).mul_left _).congr (fun n => (scale n).symm),?_⟩
  change jacobiFraction (q/E)+jacobiGeometricSeries Q (Q*(q/E))+jacobiGeometricSeries Q (Q/(q/E))=_
  rw [show Q*(q/E)= -q^3/E by dsimp [Q];ring,
    show Q/(q/E)= -q*E by dsimp [Q];field_simp [hq.ne',hp.ne']]
  rw [eu,ed,manuscriptDualVertical,tsum_congr scale,tsum_mul_left,F.tsum_add G]
  dsimp only [jacobiFraction]
  field_simp [hq.ne',hp.ne']; ring

/-- Equations two_axis_helicoid:eq-D-vertical and two_axis_helicoid:eq-G-D with all domain
restrictions derived from t>0 and 0<a<1. -/
theorem thetaG_actual_manuscript_D {t a : ℝ} (ht : 0<t) (ha : 0<a) (hb : a<1) :
    let q := Real.exp (-Real.pi/(2*t))
    let E := Real.exp (Real.pi*(a-1/2)/t)
    q/E<1 ∧ q*E<1 ∧ q^3/E<1 ∧ Summable (dualVerticalLambertTerm q E) ∧
      (thetaG t a).re= -(Real.pi^2*q/t^2)*manuscriptDualVertical q E := by
  let q := Real.exp (-Real.pi/(2*t))
  let E := Real.exp (Real.pi*(a-1/2)/t)
  have qp : 0<q := Real.exp_pos _
  have ep : 0<E := Real.exp_pos _
  have hq : q<1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (by positivity))
  have r : q/E=Real.exp (-Real.pi*a/t) := by dsimp [q,E];rw [← Real.exp_sub];congr 1;ring
  have q2 : q^2=Real.exp (-Real.pi/t) := by dsimp [q];rw [← Real.exp_nat_mul];congr 1;push_cast;ring
  have low : q/E<1 := by rw [r,Real.exp_lt_one_iff];exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha) ht
  have high : q*E<1 := by
    dsimp [q,E]
    rw [← Real.exp_add,Real.exp_lt_one_iff]
    have e : -Real.pi/(2*t)+Real.pi*(a-1/2)/t=Real.pi*(a-1)/t := by ring
    rw [e]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos (sub_neg.mpr hb)) ht
  have small : q^3/E<1 := by
    rw [show q^3/E=q^2*(q/E) by ring]
    have qsmall : q^2≤1 := by nlinarith [mul_nonneg qp.le (sub_nonneg.mpr hq.le)]
    exact ((mul_le_mul_of_nonneg_right qsmall (div_pos qp ep).le).trans_eq (one_mul _)).trans_lt low
  obtain ⟨conv,formula⟩ := jacobiRealE_eq_manuscript_D qp hq ep high small
  refine ⟨low,high,small,conv,?_⟩
  rw [thetaG_re_eq_jacobiRealE ht ha hb,← q2,← r,formula]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jacobiRealE_eq_manuscript_D
#print axioms TwoAxisHelicoid.thetaG_actual_manuscript_D
