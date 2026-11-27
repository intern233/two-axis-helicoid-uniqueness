import TwoAxisHelicoid.ZeroBranchFiniteOrientation

namespace TwoAxisHelicoid
open Complex Set

theorem axisHelicoidSide_I (α : ℝ) (P : Fin 3 → ℝ) :
    axisHelicoidSide I α 0 P = -Real.sin (α*P 2)*P 0+Real.cos (α*P 2)*P 1 := by
  simp only [axisHelicoidSide,sub_zero,
    show I*((α*P 2:ℝ):ℂ) = ((α*P 2:ℝ):ℂ)*I by ring,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]

theorem harmonic_zero_branch_bottom_side_derivative {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (α : ℝ) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a 0 z) :
    axisHelicoidSide I α 0 (X a) = 0 ∧
      ∃ e : ℝ, e < 0 ∧ HasDerivAt
        (fun y : ℝ => -axisHelicoidSide I α 0 (X ((a:ℂ)+I*y))/c) e 0 := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X a
  let γ := fun y : ℝ => (a:ℂ)+I*y
  have haL : (a:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hconj := hX.conjugation a haL
  rw [Complex.conj_ofReal] at hconj
  have h1 := congrFun hconj 1
  have h2 := congrFun hconj 2
  change X a 1 = -X a 1 at h1
  change X a 2 = -X a 2 at h2
  have hy₀ : X a 1 = 0 := by linarith
  have hh₀ : X a 2 = 0 := by linarith
  have hγ0 : γ 0 = a := by simp [γ]
  have hγ : HasDerivAt γ I 0 := by
    have h : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 0 := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
    simpa only [mul_one] using (h.const_mul I).const_add (a:ℂ)
  have hD := puncturedImmersionCoefficient_hasFDerivAt hX haL
  have hD₀ : HasFDerivAt X (nullRealDerivative p) (γ 0) := by rwa [hγ0]
  have hcoord (j : Fin 3) : HasDerivAt (fun y => X (γ y) j) ((I*(p j)).re) 0 := by
    exact ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (γ 0)
      hD₀).comp_hasDerivAt 0 hγ
  have hp2 : p 2 = 0 := by
    change puncturedImmersionCoefficient _ X a 2 = 0
    rw [hh _ haL]
    change I*c*(L.weierstrassP a-L.weierstrassP a) = 0
    ring
  obtain ⟨v,hv,hp1⟩ := harmonic_zero_branch_y_at_height_zero ht ha hc hX hh hg
  change p 1 = -I*c*v/2 at hp1
  have hZ : HasDerivAt (fun y => α*X (γ y) 2) 0 0 := by
    simpa only [hp2,mul_zero,Complex.zero_re] using (hcoord 2).const_mul α
  have hY : HasDerivAt (fun y => X (γ y) 1) (c*v/2) 0 := by
    have he := hcoord 1
    rw [hp1,show I*(-I*(c:ℂ)*v/2) = ((c*v/2:ℝ):ℂ) by
      push_cast; ring_nf; simp only [Complex.I_sq]; ring,Complex.ofReal_re] at he
    exact he
  constructor
  · simp [axisHelicoidSide_I,hy₀,hh₀]
  · refine ⟨-v/2,by linarith,?_⟩
    have h := (((hZ.sin.neg.mul (hcoord 0)).add (hZ.cos.mul hY)).neg.div_const c)
    simp only [Pi.neg_apply,hγ0,hh₀,mul_zero,Real.sin_zero,Real.cos_zero,neg_zero,zero_mul,
      zero_add,one_mul] at h
    simp_rw [axisHelicoidSide_I]
    convert h using 1
    field_simp

theorem axisHelicoidSide_I_reflection (α : ℝ) (P : Fin 3 → ℝ) :
    axisHelicoidSide I α 0 ![P 0,-P 1,-P 2] = -axisHelicoidSide I α 0 P := by
  simp [axisHelicoidSide_I]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_zero_branch_bottom_side_derivative
