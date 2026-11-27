import TwoAxisHelicoid.ZetaPoleRegular

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta thetaEtaExpression

noncomputable def spinorExponent (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  ((a : ℂ)-m)*thetaZeta t z+m*thetaEtaExpression t*z

/-- The actual scalar coefficient of the first Weierstrass spinor in §4.5. -/
noncomputable def thetaSpinor (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  exp (spinorExponent t a m z)*thetaSigma t (z-a)/thetaSigma t z

theorem spinor_multiplier_algebra (a m η z w k Z sm sz : ℂ) :
    exp ((a-m)*(Z+k)+m*η*(z+w))*(-exp (k*(z-a+w/2))*sm)/
      (-exp (k*(z+w/2))*sz) =
    exp (m*(η*w-k))*(exp ((a-m)*Z+m*η*z)*sm/sz) := by
  have he : exp ((a-m)*(Z+k)+m*η*(z+w))*exp (k*(z-a+w/2)) =
      exp (k*(z+w/2))*(exp (m*(η*w-k))*exp ((a-m)*Z+m*η*z)) := by
    simp only [← exp_add]
    congr 1
    ring
  calc
    _ = (exp ((a-m)*(Z+k)+m*η*(z+w))*exp (k*(z-a+w/2)))*sm/
        (exp (k*(z+w/2))*sz) := by ring
    _ = exp (k*(z+w/2))*(exp (m*(η*w-k))*exp ((a-m)*Z+m*η*z)*sm)/
        (exp (k*(z+w/2))*sz) := by rw [he]; congr 1; ring
    _ = _ := by rw [mul_div_mul_left _ _ (exp_ne_zero _)]; ring

theorem thetaSpinor_quasiperiod {t a : ℝ} (m : ℤ) {z w k : ℂ}
    (hσ : ∀ v, thetaSigma t (v+w) = -exp (k*(v+w/2))*thetaSigma t v)
    (hζ : thetaZeta t (z+w) = thetaZeta t z+k) :
    thetaSpinor t a m (z+w) = exp (m*(thetaEtaExpression t*w-k))*thetaSpinor t a m z := by
  unfold thetaSpinor spinorExponent
  rw [show z+w-(a : ℂ) = (z-a)+w by ring,hσ,hσ,hζ]
  exact spinor_multiplier_algebra _ _ _ _ _ _ _ _ _

theorem thetaSpinor_period_two (t a : ℝ) (m : ℤ) : Function.Periodic (thetaSpinor t a m) 2 := by
  intro z
  have h := thetaSpinor_quasiperiod (t := t) (a := a) m (z := z) (w := 2)
    (k := 2*thetaEtaExpression t) (fun v => by simpa using thetaSigma_add_two t v)
    (thetaZeta_add_two t z)
  simpa only [mul_comm (thetaEtaExpression t) 2,sub_self,mul_zero,exp_zero,one_mul] using h

theorem thetaSpinor_multiplier_half {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaSpinor t a m (z+(1+I*t)) = (-1 : ℂ)^m*thetaSpinor t a m z := by
  have h := thetaSpinor_quasiperiod (t := t) (a := a) m (z := z)
    (w := 1+I*t) (k := thetaEtaExpression t*(1+I*t)-Real.pi*I)
    (thetaSigma_add_half ht) (by simpa only [add_sub_assoc] using thetaZeta_add_half_of_pos ht ht hz)
  have he : (m : ℂ)*(thetaEtaExpression t*(1+I*t)-
      (thetaEtaExpression t*(1+I*t)-Real.pi*I)) = (m : ℂ)*(Real.pi*I) := by ring
  rw [he,exp_int_mul,exp_pi_mul_I] at h
  exact h

theorem spinorExponent_analyticAt {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (spinorExponent t a m) z := by
  have hza : AnalyticAt ℂ (thetaZeta t) z :=
    (show DifferentiableOn ℂ (thetaZeta t) (rhombicPeriodPair t ht).latticeᶜ from
      fun _ hw => (thetaZeta_hasDerivAt_of_pos ht ht hw).differentiableAt.differentiableWithinAt).analyticAt
      ((rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.mem_nhds hz)
  unfold spinorExponent
  fun_prop

theorem thetaSpinor_analyticAt {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (thetaSpinor t a m) z := by
  have hσz := thetaSigma_analyticAt ht z
  have hσa := (thetaSigma_analyticAt ht (z-a)).comp (f := fun w : ℂ => w-a) (by fun_prop)
  exact (((spinorExponent_analyticAt ht m hz).cexp).mul hσa).div hσz
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz)

theorem thetaSpinor_zero_iff {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaSpinor t a m z = 0 ↔ z-a ∈ (rhombicPeriodPair t ht).lattice := by
  unfold thetaSpinor
  rw [div_eq_zero_iff,mul_eq_zero]
  simp only [exp_ne_zero,false_or,mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz,or_false]
  exact thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)

noncomputable def spinorEndFactor (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  exp (((a : ℂ)-m)*zetaPoleRegular t z+m*thetaEtaExpression t*z)*
    thetaSigma t (z-a)/sigmaDivZero t z

theorem spinorEndFactor_analyticAt_zero {t a : ℝ} (ht : 0 < t) (m : ℤ) :
    AnalyticAt ℂ (spinorEndFactor t a m) 0 := by
  have hζ := zetaPoleRegular_analyticAt ht (Or.inr rfl)
  have hσ := (thetaSigma_analyticAt ht (0-a)).comp (f := fun w : ℂ => w-a) (by fun_prop)
  have hd := (sigmaDivZero_differentiable ht).analyticAt 0
  unfold spinorEndFactor
  fun_prop (disch := exact sigmaDivZero_ne_zero ht (Or.inr rfl))

theorem spinorEndFactor_zero_ne_zero {t a : ℝ} (ht : 0 < t)
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (m : ℤ) :
    spinorEndFactor t a m 0 ≠ 0 := by
  unfold spinorEndFactor
  apply div_ne_zero
  · apply mul_ne_zero (exp_ne_zero _)
    simp only [zero_sub,thetaSigma_neg,neg_ne_zero]
    exact mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  · exact sigmaDivZero_ne_zero ht (Or.inr rfl)

/-- The endpoint singularity is an integer pole times a single-valued
exponential and a holomorphic nonvanishing factor; no square root of the
puncture coordinate is introduced. -/
theorem thetaSpinor_endpoint_normal_form {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaSpinor t a m z = z⁻¹*exp (((a : ℂ)-m)/z)*spinorEndFactor t a m z := by
  have hn : z ≠ 0 := by intro he; apply hz; rw [he]; exact (rhombicPeriodPair t ht).lattice.zero_mem
  have hden := sigmaDivZero_ne_zero ht (Or.inl hz)
  unfold thetaSpinor spinorExponent spinorEndFactor
  rw [thetaZeta_eq_inv_add_regular ht hz,← mul_sigmaDivZero t z]
  have he : ((a : ℂ)-m)*(z⁻¹+zetaPoleRegular t z)+m*thetaEtaExpression t*z =
      ((a : ℂ)-m)/z+(((a : ℂ)-m)*zetaPoleRegular t z+m*thetaEtaExpression t*z) := by ring
  rw [he,exp_add]
  field_simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSpinor_multiplier_half
#print axioms TwoAxisHelicoid.thetaSpinor_endpoint_normal_form
