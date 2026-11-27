import TwoAxisHelicoid.JacobiRealSeries
import TwoAxisHelicoid.LambertGeometricRearrangement
import TwoAxisHelicoid.ZetaHalfPeriod
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

noncomputable def rhombicCosineTerm (Q z : ℂ) (j : ℕ) : ℂ :=
  ((j+1:ℕ):ℂ)*Q^(j+1)/(1-Q^(j+1))*Complex.cos (((j+1:ℕ):ℂ)*Real.pi*z)

private noncomputable def side (Q X : ℂ) (j : ℕ) : ℂ :=
  ((j+1:ℕ):ℂ)*(Q*X)^(j+1)/(1-Q^(j+1))

private theorem side_sum {Q X : ℂ} (q : ‖Q‖<1) (x : ‖Q*X‖<1) :
    Summable (side Q X) ∧ jacobiSecondSum Q X=∑' j, side Q X j := by
  obtain ⟨sm,eq⟩ := (geometric_lambert_orders_zero_one q x).2
  refine ⟨sm,Eq.trans (tsum_congr (fun j => ?_)) eq⟩
  rw [pow_succ,mul_assoc]

private theorem cosine_exp_powers (z : ℂ) (k : ℕ) :
    Complex.cos ((k:ℂ)*Real.pi*z)=((jacobiExp z)^k+((jacobiExp z)⁻¹)^k)/2 := by
  unfold Complex.cos jacobiExp
  rw [show (k:ℂ)*Real.pi*z*I=(k:ℂ)*(I*(Real.pi:ℂ)*z) by ring,
    show -((k:ℂ)*Real.pi*z)*I= -((k:ℂ)*(I*(Real.pi:ℂ)*z)) by ring,
    Complex.exp_neg,Complex.exp_nat_mul,inv_pow]

private theorem paired_cosine (Q z : ℂ) (j : ℕ) :
    side Q (jacobiExp z) j+side Q (jacobiExp z)⁻¹ j=2*rhombicCosineTerm Q z j := by
  unfold side rhombicCosineTerm
  rw [cosine_exp_powers,mul_pow,mul_pow]
  ring

private theorem principal_sine {z : ℂ} (hx : jacobiExp z≠1) :
    -(Real.pi:ℂ)^2*(jacobiExp z/(1-jacobiExp z)^2)=
      (Real.pi:ℂ)^2/4/Complex.sin ((Real.pi:ℂ)*z/2)^2 := by
  let X := jacobiExp z
  let w := (Real.pi:ℂ)*z/2
  have xn : X≠0 := jacobiExp_ne_zero z
  have hd : 1-X≠0 := sub_ne_zero.mpr hx.symm
  have cs : Complex.cos ((Real.pi:ℂ)*z)=(X+X⁻¹)/2 := by
    simpa only [Nat.cast_one,one_mul,pow_one] using cosine_exp_powers z 1
  have double := Complex.cos_two_mul_eq_one_sub w
  rw [show 2*w=(Real.pi:ℂ)*z by dsimp [w];ring,cs] at double
  field_simp [xn] at double
  have den : (1-X)^2= -(4*X*(Complex.sin w)^2) := by linear_combination double
  have sn : Complex.sin w≠0 := by
    intro zero
    exact (pow_ne_zero 2 hd) (by simpa [zero] using den)
  change -(Real.pi:ℂ)^2*(X/(1-X)^2)=(Real.pi:ℂ)^2/4/(Complex.sin w)^2
  rw [den]
  field_simp [xn,sn]

private theorem strip_sides (s : ℝ) (z : ℂ) :
    (‖jacobiNome s*jacobiExp z‖<1 ↔ -s<z.im) ∧
      (‖jacobiNome s*(jacobiExp z)⁻¹‖<1 ↔ z.im<s) := by
  have xn : ‖jacobiExp z‖=Real.exp (-Real.pi*z.im) := by
    unfold jacobiExp
    rw [show I*(Real.pi:ℂ)*z=((Real.pi:ℂ)*z)*I by ring,Complex.norm_exp_mul_I,
      Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,neg_mul]
  have xi : ‖(jacobiExp z)⁻¹‖=Real.exp (Real.pi*z.im) := by
    rw [norm_inv,xn,neg_mul,Real.exp_neg,inv_inv]
  simp only [norm_mul,jacobiNome_norm,xn,xi,← Real.exp_add,Real.exp_lt_one_iff]
  constructor
  · constructor
    · intro h
      by_contra! h'
      nlinarith [mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (show s+z.im≤0 by linarith)]
    · intro h
      nlinarith [mul_pos Real.pi_pos (show 0<s+z.im by linarith)]
  · constructor
    · intro h
      by_contra! h'
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h')]
    · intro h
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr h)]

private theorem side_not_summable {Q X : ℂ} (q : ‖Q‖<1) (big : 1≤‖Q*X‖) : ¬Summable (side Q X) := by
  intro sm
  have toZero : Tendsto (fun j => ‖side Q X j‖) atTop (𝓝 0) := by
    simpa using sm.tendsto_atTop_zero.norm
  obtain ⟨j,hj⟩ := (toZero.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).exists
  let k := j+1
  have lt : ‖Q^k‖<1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg Q) q (Nat.succ_ne_zero j)
  have dn : 0<‖1-Q^k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => lt.ne (by rw [← h,norm_one])))
  have top : ‖1-Q^k‖≤2 := (norm_sub_le _ _).trans (by rw [norm_one];linarith)
  have k1 : (1:ℕ)≤k := Nat.succ_le_succ (Nat.zero_le j)
  have large : 1 ≤ (k:ℝ)*‖Q*X‖^k :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast k1) (one_le_pow₀ big)
  change ‖((k:ℂ)*(Q*X)^k)/(1-Q^k)‖<1/2 at hj
  rw [norm_div,norm_mul,Complex.norm_natCast,norm_pow,div_lt_iff₀ dn] at hj
  linarith

private theorem cosine_series_annulus {Q : ℂ} (q : ‖Q‖<1) (z : ℂ) :
    Summable (rhombicCosineTerm Q z) ↔ ‖Q*jacobiExp z‖<1 ∧ ‖Q*(jacobiExp z)⁻¹‖<1 := by
  let X := jacobiExp z
  constructor
  · intro sm
    have both : Summable (fun j => side Q X j+side Q X⁻¹ j) :=
      (sm.mul_left 2).congr (fun j => (paired_cosine Q z j).symm)
    by_cases hp : ‖Q*X‖<1
    · have negSide : Summable (side Q X⁻¹) :=
        (both.sub (side_sum q hp).1).congr (fun j => by
          change (side Q X j + side Q X⁻¹ j) - side Q X j = side Q X⁻¹ j
          abel)
      exact ⟨hp,lt_of_not_ge (fun h => side_not_summable q h negSide)⟩
    · have product : ‖Q*X‖*‖Q*X⁻¹‖<1 := by
        rw [norm_mul,norm_mul,norm_inv,show ‖Q‖*‖X‖*(‖Q‖*‖X‖⁻¹)=‖Q‖^2 by
          calc
            _ = ‖Q‖^2 * (‖X‖ * ‖X‖⁻¹) := by ring
            _ = _ := by rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (jacobiExp_ne_zero z : X ≠ 0)), mul_one]]
        exact pow_lt_one₀ (norm_nonneg Q) q (by decide : 2≠0)
      have hm : ‖Q*X⁻¹‖<1 := by
        by_contra! high
        exact product.not_ge (one_le_mul_of_one_le_of_one_le (le_of_not_gt hp) high)
      have posSide : Summable (side Q X) :=
        (both.sub (side_sum q hm).1).congr (fun j => by
          change (side Q X j + side Q X⁻¹ j) - side Q X⁻¹ j = side Q X j
          abel)
      exact False.elim (side_not_summable q (le_of_not_gt hp) posSide)
  · rintro ⟨hp,hm⟩
    apply (((side_sum q hp).1.add (side_sum q hm).1).div_const (2:ℂ)).congr
    intro j
    change (side Q (jacobiExp z) j+side Q (jacobiExp z)⁻¹ j)/2=_
    rw [paired_cosine]
    ring

/-- The cosine series in Section 7 converges exactly in the open
horizontal strip, excluding both boundary lines. -/
theorem rhombic_cosine_series_summable_iff {s : ℝ} (hs : 0<s) (z : ℂ) :
    Summable (rhombicCosineTerm (jacobiNome s) z) ↔ |z.im|<s := by
  rw [cosine_series_annulus (jacobiNome_norm_lt_one hs),abs_lt,
    (strip_sides s z).1,(strip_sides s z).2]

theorem rhombic_cosine_series_absolutely_summable_iff {s : ℝ} (hs : 0<s) (z : ℂ) :
    Summable (fun j => ‖rhombicCosineTerm (jacobiNome s) z j‖) ↔ |z.im|<s :=
  summable_norm_iff.trans (rhombic_cosine_series_summable_iff hs z)

/-- The actual complex Weierstrass function and its half-period
quasiperiod give the printed cosecant and cosine expansion off the
lattice, throughout the full strip of convergence. -/
theorem rhombic_weierstrass_cosine_series {s : ℝ} (hs : 0<s) {z : ℂ} (strip : |z.im|<s)
    (hz : z∉(rhombicPeriodPair s hs).lattice) :
    let q : ℂ := Real.exp (-Real.pi*s/2)
    let Q := -q^2
    Summable (rhombicCosineTerm Q z) ∧
      (rhombicPeriodPair s hs).weierstrassP z+thetaZeta s 1=
        (Real.pi:ℂ)^2/4/Complex.sin ((Real.pi:ℂ)*z/2)^2-
        2*(Real.pi:ℂ)^2*(∑' j, rhombicCosineTerm Q z j) := by
  have nome : jacobiNome s= -((Real.exp (-Real.pi*s/2):ℂ)^2) := by
    rw [jacobiNome_eq_neg_exp,← Complex.ofReal_pow,← Real.exp_nat_mul,
      show ((2:ℕ):ℝ)*(-Real.pi*s/2)= -Real.pi*s by push_cast;ring]
  dsimp only
  rw [← nome,thetaZeta_one]
  let Q := jacobiNome s
  let X := jacobiExp z
  have q : ‖Q‖<1 := jacobiNome_norm_lt_one hs
  have hp := (strip_sides s z).1.mpr (abs_lt.mp strip).1
  have hm := (strip_sides s z).2.mpr (abs_lt.mp strip).2
  have xn : X≠1 := by
    intro one
    have nonzero := mul_ne_zero (jacobiTheta_normalization_ne_zero hs)
      (mt (thetaScaledJet_zero_iff_lattice_of_pos hs hs z).mp hz)
    apply nonzero
    rw [← rhombicProductTheta_eq_scaled_theta hs]
    change Complex.exp _*((1-X)*jacobiFactorProduct Q X*jacobiFactorProduct Q X⁻¹)=0
    rw [one,sub_self,zero_mul,zero_mul,mul_zero]
  have sm := (rhombic_cosine_series_summable_iff hs z).mpr strip
  refine ⟨sm,?_⟩
  rw [weierstrassP_add_eta_eq_jacobiSecondE hs hz xn (by simpa only [norm_mul] using hp)
    (by simpa only [norm_mul] using hm)]
  have series : jacobiSecondSum Q X+jacobiSecondSum Q X⁻¹=2*(∑' j, rhombicCosineTerm Q z j) := by
    rw [(side_sum q hp).2,(side_sum q hm).2,← (side_sum q hp).1.tsum_add (side_sum q hm).1,← tsum_mul_left]
    exact tsum_congr (paired_cosine Q z)
  change -(Real.pi:ℂ)^2*(X/(1-X)^2+jacobiSecondSum Q X+jacobiSecondSum Q X⁻¹)=_
  rw [add_assoc,series,mul_add,principal_sine xn]
  ring

/-- Both pairings printed in Section 7 at r=q, including strict
positivity of the absolutely convergent series of positive terms. -/
theorem jacobiRealE_at_q_positive_series {q : ℝ} (q0 : 0<q) (q1 : q<1) :
    let B := fun k : ℕ => jacobiFraction (q^(2*k+1))+jacobiFraction (-q^(2*k+1))
    let C := fun k : ℕ => 4*q^(4*k+2)/(1-q^(4*k+2))^2
    Summable C ∧ (∀ k, 0<C k) ∧ jacobiRealE (-q^2) q=(∑' k, B k) ∧
      (∑' k, B k)=(∑' k, C k) ∧ 0<(∑' k, C k) := by
  have Q : |-q^2|<1 := by rw [abs_neg,abs_sq];nlinarith
  have a : |q|<1 := by rwa [abs_of_pos q0]
  have b : |-q|<1 := by rwa [abs_neg]
  let F := fun k : ℕ => jacobiFraction ((-q^2)^k*q)+jacobiFraction ((-q^2)^k*(-q))
  let B := fun k : ℕ => jacobiFraction (q^(2*k+1))+jacobiFraction (-q^(2*k+1))
  let C := fun k : ℕ => 4*q^(4*k+2)/(1-q^(4*k+2))^2
  have sf : Summable F := (jacobiGeometricSeries_summable Q a).add (jacobiGeometricSeries_summable Q b)
  have val : jacobiRealE (-q^2) q=∑' k, F k := by
    unfold jacobiRealE
    rw [show -q^2/q= -q by field_simp [q0.ne'],← jacobiGeometricSeries_split Q a]
    exact ((jacobiGeometricSeries_summable Q a).tsum_add (jacobiGeometricSeries_summable Q b)).symm
  have p (k : ℕ) : F k=C k := by
    have bound := (jacobi_geometric_argument_abs_le (a := q) Q k).trans_lt a
    dsimp only [F,C]
    rw [show (-q^2)^k*(-q)= -((-q^2)^k*q) by ring,jacobiFraction_pair bound]
    have sq : ((-q^2)^k*q)^2=q^(4*k+2) := by
      rw [mul_pow,← pow_mul,Nat.mul_comm k 2,pow_mul,show (-q^2)^2=q^4 by ring,← pow_mul,← pow_add]
    rw [sq]
  have r (k : ℕ) : B k=C k := by
    have bound : |q^(2*k+1)|<1 := by
      rw [abs_of_pos (pow_pos q0 _)]
      exact pow_lt_one₀ q0.le q1 (by omega)
    dsimp only [B,C]
    rw [jacobiFraction_pair bound,← pow_mul,show (2*k+1)*2=4*k+2 by omega]
  have eq : jacobiRealE (-q^2) q=∑' k, C k := val.trans (tsum_congr p)
  have pos (k : ℕ) : 0<C k := by
    have lt : q^(4*k+2)<1 := pow_lt_one₀ q0.le q1 (by omega)
    exact div_pos (mul_pos (by norm_num) (pow_pos q0 _)) (sq_pos_of_pos (sub_pos.mpr lt))
  exact ⟨sf.congr p,pos,eq.trans (tsum_congr r).symm,tsum_congr r,eq ▸ jacobiRealE_at_q_pos q0 q1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_cosine_series_summable_iff
#print axioms TwoAxisHelicoid.rhombic_cosine_series_absolutely_summable_iff
#print axioms TwoAxisHelicoid.rhombic_weierstrass_cosine_series
#print axioms TwoAxisHelicoid.jacobiRealE_at_q_positive_series
