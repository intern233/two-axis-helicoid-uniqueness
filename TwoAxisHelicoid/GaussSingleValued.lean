import TwoAxisHelicoid.GaussRealCoefficients
import TwoAxisHelicoid.UnrestrictedGauss
import TwoAxisHelicoid.GaussMultiplierRigidity

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaZeta thetaEtaExpression thetaGauss
set_option maxHeartbeats 1200000

theorem gaussLogPoleSet_neg {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    -z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a := by
  obtain ⟨hz₀,hm,hp⟩ := (not_mem_gaussLogPoleSet _ _ _).mp hz
  apply (not_mem_gaussLogPoleSet _ _ _).mpr
  refine ⟨fun h => hz₀ (by simpa only [neg_neg] using (rhombicPeriodPair t ht).lattice.neg_mem h),?_,?_⟩
  · intro h
    apply hp
    have he : -(-z-(a : ℂ)) = z+a := by ring
    exact he ▸ (rhombicPeriodPair t ht).lattice.neg_mem h
  · intro h
    apply hm
    have he : -(-z+(a : ℂ)) = z-a := by ring
    exact he ▸ (rhombicPeriodPair t ht).lattice.neg_mem h

theorem unrestrictedGauss_neg_product {t : ℝ} (ht : 0 < t) (a : ℝ) (κ β : ℂ) {z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    unrestrictedGauss t a κ β (-z)*unrestrictedGauss t a κ β z = 1 := by
  have hsm := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mp hm
  have hsp := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
  have hmz : -z-a = -(z+a) := by ring
  have hpz : -z+a = -(z-a) := by ring
  have he : -κ*thetaZeta t (-z)+β*(-z) = -(-κ*thetaZeta t z+β*z) := by
    rw [thetaZeta_neg]
    ring
  unfold unrestrictedGauss
  rw [he,Complex.exp_neg,hmz,hpz,thetaSigma_neg,thetaSigma_neg]
  field_simp

/-- Actual single-valuedness on the two primitive periods quantizes the
unrestricted model. Only one regular point is needed to cancel each
nonzero multiplier. -/
theorem unrestrictedGauss_periods_quantize {t a κ β : ℝ} (ht : 0 < t)
    {z : ℂ} (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a)
    (h₂ : unrestrictedGauss t a κ β (z+2) = unrestrictedGauss t a κ β z)
    (hτ : unrestrictedGauss t a κ β (z+(1+I*t)) = unrestrictedGauss t a κ β z) :
    ∃ m : ℤ, κ = 2*((m : ℝ)-a) ∧ β = 2*(m : ℝ)*(thetaEtaExpression t).re := by
  obtain ⟨hz₀,hm,hp⟩ := (not_mem_gaussLogPoleSet _ _ _).mp hz
  have hn := unrestrictedGauss_ne_zero ht a κ β hm hp
  have hη : thetaEtaExpression t = ((thetaEtaExpression t).re : ℂ) := by
    apply Complex.ext <;> simp [thetaEtaExpression_real]
  have hq₂ := unrestrictedGauss_quasiperiod (t := t) (a := a) κ β (z := z) (w := 2)
    (k := 2*thetaEtaExpression t) (fun v => by simpa using thetaSigma_add_two t v)
    (thetaZeta_add_two t z)
  have he₂ : Complex.exp ((β : ℂ)*2-((κ : ℂ)+2*a)*(2*thetaEtaExpression t)) = 1 := by
    apply mul_right_cancel₀ hn
    rw [← hq₂,h₂,one_mul]
  have hqτ := unrestrictedGauss_quasiperiod (t := t) (a := a) κ β (z := z) (w := 1+I*t)
    (k := thetaEtaExpression t*(1+I*t)-Real.pi*I) (thetaSigma_add_half ht)
    (by simpa only [add_sub_assoc] using thetaZeta_add_half_of_pos ht ht hz₀)
  have heτ : Complex.exp ((β : ℂ)*(1+I*t)-((κ : ℂ)+2*a)*
      (thetaEtaExpression t*(1+I*t)-Real.pi*I)) = 1 := by
    apply mul_right_cancel₀ hn
    rw [← hqτ,hτ,one_mul]
  apply gauss_real_multiplier_quantization a κ β (thetaEtaExpression t).re t
  · rw [hη] at he₂
    convert he₂ using 1
    push_cast
    ring
  · rw [hη] at heτ
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat] using heτ

theorem thetaGauss_eq_I_mul_unrestricted (t a : ℝ) (m : ℤ) (z : ℂ) :
    thetaGauss t a m z = I*unrestrictedGauss t a (2*((m : ℂ)-a))
      (2*(m : ℂ)*thetaEtaExpression t) z := by
  unfold thetaGauss unrestrictedGauss
  have he : 2*((a : ℂ)-m)*thetaZeta t z+2*m*thetaEtaExpression t*z =
      -(2*((m : ℂ)-a))*thetaZeta t z+(2*m*thetaEtaExpression t)*z := by ring
  rw [he]
  ring

/-- Once the logarithmic differential has been classified with real
coefficients, connectedness, actual periods and the half-turn symmetry
recover the complete integer Gauss family, up to its harmless sign. -/
theorem gauss_closed_real_log_differential_integer_family {t a κ β : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, DifferentiableAt ℂ g z)
    (hgn : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z ≠ 0)
    (hlog : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      deriv g z/g z = (κ : ℂ)*(rhombicPeriodPair t ht).weierstrassP z+β+
        thetaZeta t (z-a)-thetaZeta t (z+a))
    (hperiod : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a → g (z+ω) = g z)
    (hneg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (-z)*g z = -1) :
    ∃ m : ℤ, κ = 2*((m : ℝ)-a) ∧ β = 2*(m : ℝ)*(thetaEtaExpression t).re ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = -thetaGauss t a m z)) := by
  let L := rhombicPeriodPair t ht
  let S := gaussLogPoleSet L a
  have hfin : ({0,(a : ℂ),-(a : ℂ)} : Set ℂ).Finite := by simp
  have hs : IsOpen Sᶜ := (latticePoleSet_isClosed L hfin).isOpen_compl
  have hsc : IsConnected Sᶜ :=
    (latticePoleSet_countable L hfin.countable).isConnected_compl_of_one_lt_rank (by simp)
  have hregular (z : ℂ) (hz : z ∈ Sᶜ) :
      z ∉ L.lattice ∧ z-a ∉ L.lattice ∧ z+a ∉ L.lattice :=
    (not_mem_gaussLogPoleSet _ _ _).mp hz
  obtain ⟨C,hC,hgC⟩ := equal_logarithmic_derivatives_constant_ratio hs hsc
    (f := unrestrictedGauss t a κ β) (g := g)
    (fun z hz => (unrestrictedGauss_hasDerivAt ht a κ β
      (hregular z hz).1 (hregular z hz).2.1 (hregular z hz).2.2).differentiableAt)
    hg (fun z hz => unrestrictedGauss_ne_zero ht a κ β (hregular z hz).2.1 (hregular z hz).2.2)
    hgn (fun z hz => by rw [hlog z hz,unrestrictedGauss_log_derivative ht a κ β
      (hregular z hz).1 (hregular z hz).2.1 (hregular z hz).2.2])
  let z : ℂ := ((a/2 : ℝ) : ℂ)
  have hz : z ∉ S := real_below_a_not_mem_gaussLogPoleSet ht ha
    ⟨by linarith [ha.1],by linarith [ha.1]⟩
  have hmodel (ω : ℂ) (hω : ω ∈ L.lattice) :
      unrestrictedGauss t a κ β (z+ω) = unrestrictedGauss t a κ β z := by
    have hzω : z+ω ∉ S := (latticePoleSet_add_iff L _ z ω hω).not.mpr hz
    apply mul_left_cancel₀ hC
    rw [← hgC _ hzω,← hgC _ hz,hperiod z ω hω hz]
  obtain ⟨m,hκ,hβ⟩ := unrestrictedGauss_periods_quantize ht hz
    (hmodel 2 L.ω₁_mem_lattice) (hmodel (1+I*t) L.ω₂_mem_lattice)
  have hCsq : C^2 = -1 := by
    have hn := hneg z hz
    rw [hgC (-z) (gaussLogPoleSet_neg ht hz),hgC z hz] at hn
    have hm := unrestrictedGauss_neg_product ht a κ β (hregular z hz).2.1 (hregular z hz).2.2
    calc
      C^2 = C^2*(unrestrictedGauss t a κ β (-z)*unrestrictedGauss t a κ β z) := by rw [hm,mul_one]
      _ = -1 := by linear_combination hn
  have hCI : C = I ∨ C = -I := sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hCsq,I_sq])
  have hκc : (κ : ℂ) = 2*((m : ℂ)-a) := by exact_mod_cast hκ
  have hβc : (β : ℂ) = 2*(m : ℂ)*thetaEtaExpression t := by
    have hη : thetaEtaExpression t = ((thetaEtaExpression t).re : ℂ) := by
      apply Complex.ext <;> simp [thetaEtaExpression_real]
    rw [hη]
    exact_mod_cast hβ
  refine ⟨m,hκ,hβ,?_⟩
  rcases hCI with hCI | hCI
  · left
    intro w hw
    rw [hgC w hw,hCI,hκc,hβc,thetaGauss_eq_I_mul_unrestricted]
  · right
    intro w hw
    rw [hgC w hw,hCI,hκc,hβc,thetaGauss_eq_I_mul_unrestricted]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.gauss_closed_real_log_differential_integer_family
