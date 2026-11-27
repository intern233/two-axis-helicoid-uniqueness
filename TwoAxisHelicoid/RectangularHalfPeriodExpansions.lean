import TwoAxisHelicoid.RectangularHalfPeriodReduction
import TwoAxisHelicoid.HalfPeriodOriginalLambert

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaZeta markedWeierstrassZeta

/-- Both rectangular half-period constants transform in the fixed physical
normalization, including the inhomogeneous term for zeta. -/
theorem rectangular_half_period_inversion {t : ℝ} (ht : 0<t) :
    let R := manuscriptRectangularLattice t ht
    let s := 1/t
    let S := manuscriptRectangularLattice s (one_div_pos.mpr ht)
    markedWeierstrassZeta R 1=(Real.pi:ℂ)/(2*t)-markedWeierstrassZeta S 1/(t:ℂ)^2 ∧
    R.weierstrassP (1+I*t)= -S.weierstrassP (1+I*s)/(t:ℂ)^2 := by
  let R := manuscriptRectangularLattice t ht
  let s := 1/t
  let S := manuscriptRectangularLattice s (one_div_pos.mpr ht)
  obtain ⟨w,z,_⟩ := actual_rectangular_half_period_reduction ht
  obtain ⟨w',z',_⟩ := actual_rectangular_half_period_reduction (one_div_pos.mpr ht)
  have wv := rhombic_weierstrassP_one_reciprocal ht
  have zv := thetaEtaExpression_reciprocal ht
  rw [w,w'] at wv
  rw [← thetaZeta_one,← thetaZeta_one,z,z'] at zv
  have we : R.weierstrassP (1+I*t)= -S.weierstrassP (1+I*s)/(t:ℂ)^2 := by linear_combination -wv/2
  refine ⟨?_,we⟩
  change markedWeierstrassZeta R 1=(Real.pi:ℂ)/(2*t)-markedWeierstrassZeta S 1/(t:ℂ)^2
  change 2*markedWeierstrassZeta R 1+R.weierstrassP (1+I*t)=
    (Real.pi:ℂ)/t-(2*markedWeierstrassZeta S 1+S.weierstrassP (1+I*s))/(t:ℂ)^2 at zv
  rw [we] at zv
  linear_combination zv/2

/-- The two unnumbered Lambert expansions adjoining the rectangular
zeta formula in section 5, for the actual rectangular periods. -/
theorem rectangular_half_period_lambert {t : ℝ} (ht : 0<t) :
    let R := manuscriptRectangularLattice t ht
    let q := Real.exp (-Real.pi*t)
    let U := fun n : ℕ => (n+1:ℝ)*((-1:ℝ)^(n+1)*q^(n+1))/(1-q^(2*(n+1)))
    let V := fun n : ℕ => (n+1:ℝ)*q^(2*(n+1))/(1-q^(2*(n+1)))
    Summable U ∧ Summable V ∧
      markedWeierstrassZeta R 1=((Real.pi^2/12-2*Real.pi^2*∑' n,V n : ℝ):ℂ) ∧
      R.weierstrassP (1+I*t)= -markedWeierstrassZeta R 1-((2*Real.pi^2*∑' n,U n : ℝ):ℂ) := by
  let R := manuscriptRectangularLattice t ht
  let q := Real.exp (-Real.pi*t)
  let U := fun n : ℕ => (n+1:ℝ)*((-1:ℝ)^(n+1)*q^(n+1))/(1-q^(2*(n+1)))
  let V := fun n : ℕ => (n+1:ℝ)*q^(2*(n+1))/(1-q^(2*(n+1)))
  let T := fun n : ℕ => (n+1:ℝ)*((-1:ℝ)^(n+1)*q^(n+1)-3*q^(2*(n+1)))/(1-q^(2*(n+1)))
  let L := fun n : ℕ => (n+1:ℝ)*(-q)^(n+1)/(1-(-q)^(n+1))
  have hq : |q|<1 := by rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff];exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) ht
  have hq2 : ‖q^2‖<1 := by rw [Real.norm_eq_abs,abs_pow];exact pow_lt_one₀ (abs_nonneg q) hq (by decide)
  have v : Summable V := by
    have h := summable_norm_pow_mul_geometric_div_one_sub 1 hq2
    simpa only [V,pow_mul,pow_one,Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  obtain ⟨conv,fval⟩ := ellipticFReal_manuscript_signed_lambert ht
  change Summable T at conv
  change ellipticFReal t=Real.pi^2/4+2*Real.pi^2*∑' n,T n at fval
  have eqT (n : ℕ) : T n=U n-3*V n := by dsimp only [T,U,V];ring
  have u : Summable U := (conv.add (v.mul_left 3)).congr (fun n => by change T n+3*V n=U n;rw [eqT];ring)
  have eqL (n : ℕ) : L n=U n+V n := by
    let x := (-q)^(n+1)
    have ax : |x|<1 := by dsimp [x];rw [abs_pow,abs_neg];exact pow_lt_one₀ (abs_nonneg q) hq (Nat.succ_ne_zero n)
    have hx := abs_lt.mp ax
    have den : 1-x^2≠0 := by nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith : 0<1+x)]
    have sign : (-1:ℝ)^(n+1)*q^(n+1)=x := by rw [← mul_pow];simp [x]
    have base : q^(2*(n+1))=x^2 := by
      calc q^(2*(n+1))=(q^2)^(n+1) := pow_mul _ _ _
           _=((-q)^2)^(n+1) := by rw [neg_sq]
           _=(-q)^(2*(n+1)) := (pow_mul _ _ _).symm
           _=(-q)^((n+1)*2) := by rw [Nat.mul_comm 2 (n+1)]
           _=x^2 := pow_mul _ _ _
    change (n+1:ℝ)*x/(1-x)=_+_
    dsimp only [U,V]
    rw [sign,base]
    field_simp [den,sub_ne_zero.mpr (ne_of_gt hx.2)]
    ring
  rw [tsum_congr eqT,u.tsum_sub (v.mul_left 3),tsum_mul_left] at fval
  have eta := actual_eta_lambert_expansion ht
  change thetaZeta t 1=((Real.pi^2/12*(1-24*∑' n,L n):ℝ):ℂ) at eta
  rw [tsum_congr eqL,u.tsum_add v] at eta
  let Z := markedWeierstrassZeta R 1
  let E := R.weierstrassP (1+I*t)
  obtain ⟨val,inc,f⟩ := actual_rectangular_half_period_reduction ht
  change (rhombicPeriodPair t ht).weierstrassP 1= -2*E at val
  change thetaZeta t 1=2*Z+E at inc
  change ellipticFReal t=(2*Z-E).re at f
  rw [eta] at inc
  have er := rhombic_weierstrassP_real ht 1
  rw [Complex.ofReal_one,val] at er
  have zr := congrArg Complex.re inc
  have zi := congrArg Complex.im inc
  change Real.pi^2/12*(1-24*((∑' n,U n)+(∑' n,V n)))=(2*Z+E).re at zr
  change 0=(2*Z+E).im at zi
  norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.neg_re,Complex.neg_im] at er zr zi f
  refine ⟨u,v,?_,?_⟩
  · change Z=_
    apply Complex.ext
    · change Z.re=Real.pi^2/12-2*Real.pi^2*(∑' n,V n)
      nlinarith only [zr,f,fval]
    · rw [Complex.ofReal_im]; linarith only [zi,er]
  · change E= -Z-_
    apply Complex.ext
    · rw [Complex.sub_re,Complex.neg_re,Complex.ofReal_re]
      change E.re= -Z.re-2*Real.pi^2*(∑' n,U n)
      nlinarith only [zr,f,fval]
    · rw [Complex.sub_im,Complex.neg_im,Complex.ofReal_im]; linarith only [zi,er]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangular_half_period_inversion
#print axioms TwoAxisHelicoid.rectangular_half_period_lambert
