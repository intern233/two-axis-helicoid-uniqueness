import TwoAxisHelicoid.ZeroBranchHorizontalPeriod
import TwoAxisHelicoid.AxisHelicoidCalibration

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate
attribute [local irreducible] thetaA thetaGauss thetaZeta thetaSigma thetaScaledJet

/-- The normalized Gauss phase at the common axis point is fixed even
when the height scale changes sign or the integer changes parity. -/
theorem thetaGauss_axis_midpoint_eq_I {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) : thetaGauss t a m (I*t) = I := by
  have hr : (1-(a:ℂ)) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_sub,Complex.ofReal_one] using
      real_not_mem_rhombic_lattice_of_pos ht (show 0 < 1-a by linarith [ha.2])
        (show 1-a < 2 by linarith [ha.1])
  have hnr := mt (thetaSigma_zero_iff_lattice_of_pos ht ht _).mp hr
  have hs := thetaSigma_add_two t (-(1-(a:ℂ)))
  rw [show -(1-(a:ℂ))+2 = 1+a by ring,show -(1-(a:ℂ))+1 = a by ring,thetaSigma_neg,
    neg_mul_neg] at hs
  have h1 : thetaGauss t a m 1 = I := by
    rw [thetaGauss,thetaZeta_one,hs,show 2*((a:ℂ)-m)*thetaEtaExpression t+
        2*m*thetaEtaExpression t*1 = 2*thetaEtaExpression t*a by ring]
    field_simp
  have h1reg : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_one] using
      real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num)
  have hn : (-1:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by simpa using h1reg
  rw [show I*(t:ℂ) = -1+(1+I*t) by ring,thetaGauss_period_half_of_pos ht ht m hn]
  have hp := thetaGauss_period_two t a m (-1)
  norm_num at hp
  exact hp.symm.trans h1

theorem zeroBranchKernel_real_nonneg (t a x : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ zeroBranchKernel t a x = (v:ℂ) := by
  let J := fun j y => (thetaScaledJet t j (y:ℂ)).re
  let v := (J 1 0/J 0 a)^2*(J 0 (x-a)/J 0 x)^2*Real.exp (2*a*(J 1 x/J 0 x))
  refine ⟨v,by dsimp only [v]; positivity,?_⟩
  rw [zeroBranchKernel_scaled,show (x:ℂ)-a = ((x-a:ℝ):ℂ) by push_cast; ring,
    ← Complex.ofReal_zero,thetaScaledJet_eq_ofReal t 1 0,thetaScaledJet_eq_ofReal t 0 a,
    thetaScaledJet_eq_ofReal t 0 (x-a),thetaScaledJet_eq_ofReal t 0 x,thetaScaledJet_eq_ofReal t 1 x]
  dsimp only [v,J]
  push_cast
  rfl

theorem zeroBranchKernel_divisor_values {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    zeroBranchKernel t a a = 0 ∧
      ∃ v : ℝ, 0 < v ∧ zeroBranchKernel t a (-(a:ℂ)) = (v:ℂ) := by
  have hL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h2 : ((a:ℂ)+(a:ℂ)) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_add] using real_not_mem_rhombic_lattice_of_pos ht
      (show (0:ℝ) < a+a by linarith [ha.1]) (show a+a < 2 by linarith [ha.2])
  have hz : thetaA t a a = 0 := (thetaA_zero_iff_shift_lattice ht hL hL).mpr (by simp)
  refine ⟨by rw [zeroBranchKernel,hz,mul_zero],?_⟩
  obtain ⟨v,hv,he⟩ := zeroBranchKernel_real_nonneg t a (-a)
  rw [Complex.ofReal_neg] at he
  refine ⟨v,lt_of_le_of_ne hv ?_,he⟩
  intro hv0
  rw [← hv0,Complex.ofReal_zero,zeroBranchKernel] at he
  have hN := (thetaA_zero_iff_shift_lattice ht hL (z := -(a:ℂ)) (by simpa using hL)).mp
    ((mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _))
  exact h2 (by simpa only [show -(a:ℂ)-a = -(a+a) by ring,neg_mem_iff] using hN)

theorem zeroBranch_y_coefficient {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    weierstrassTriple (thetaGauss t a 0 z) (coordinateData t a c ht z 2) 1 =
      I*c/2*(zeroBranchKernel t a z-zeroBranchKernel t a (-z)) := by
  obtain ⟨hL,hm,hp⟩ := (not_mem_gaussLogPoleSet _ _ _).mp hz
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h := thetaGauss_zero_height_kernel ht c haL hL hp
  have hn := thetaGauss_zero_height_kernel ht c haL (z := -z) (by simpa using hL)
    (by simpa only [show -z+(a:ℂ) = -(z-a) by ring,neg_mem_iff] using hm)
  have hh : coordinateData t a c ht (-z) 2 = coordinateData t a c ht z 2 := by
    change I*c*((rhombicPeriodPair t ht).weierstrassP (-z)-_) = _
    rw [(rhombicPeriodPair t ht).weierstrassP_neg]
    rfl
  have hne := thetaGauss_ne_zero ht a 0 hm hp
  have he : thetaGauss t a 0 (-z) = -(thetaGauss t a 0 z)⁻¹ := by
    apply mul_right_cancel₀ hne
    rw [thetaGauss_neg_product ht a 0 hm hp]
    simp [hne]
  rw [he,hh] at hn
  change I*(_⁻¹+_)/2*_ = _
  linear_combination I*(h-hn)/2

theorem harmonic_zero_branch_y_at_height_zero {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a 0 z) :
    ∃ v : ℝ, 0 < v ∧
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X a 1 = -I*c*v/2 := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X
  let k := zeroBranchKernel t a
  have haL : (a:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hA := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  have he : (fun z => p z 1) =ᶠ[𝓝[≠] (a:ℂ)] fun z => I*c/2*(k z-k (-z)) := by
    filter_upwards [latticePoleSet_punctured_avoids L (show ({0,(a:ℂ),-(a:ℂ)} : Set ℂ).Finite by simp)
      (a:ℂ)] with z hz
    change z ∉ gaussLogPoleSet L a at hz
    have hL := ((not_mem_gaussLogPoleSet _ _ _).mp hz).1
    have hhn := null_height_nonzero_away_pair ht ha
      (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hh hz
    change puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 1 = _
    rw [null_eq_weierstrassTriple (hA.null z hL) hhn,hg z hz,hh z hL]
    exact zeroBranch_y_coefficient ht ha hz
  have hca : ContinuousAt k (a:ℂ) := (zeroBranchKernel_differentiableAt ht a haL).continuousAt
  have hcn : ContinuousAt (fun z : ℂ => k (-z)) (a:ℂ) :=
    (zeroBranchKernel_differentiableAt ht a (z := -(a:ℂ)) (by simpa using haL)).continuousAt.comp
      continuous_neg.continuousAt
  have hh' : p a 1 = I*c/2*(k a-k (-a)) := tendsto_nhds_unique
    ((puncturedImmersionCoefficient_analyticAt hX haL 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (((hca.sub hcn).const_mul _).tendsto.mono_left nhdsWithin_le_nhds |>.congr' he.symm)
  obtain ⟨haK,v,hv,hnK⟩ := zeroBranchKernel_divisor_values ht ha
  refine ⟨v,hv,?_⟩
  change p a 1 = _
  change p a 1 = I*c/2*(zeroBranchKernel t a a-zeroBranchKernel t a (-a)) at hh'
  rw [hh',haK,hnK]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.thetaGauss_axis_midpoint_eq_I
#print axioms TwoAxisHelicoid.harmonic_zero_branch_y_at_height_zero
