import TwoAxisHelicoid.ComplexThetaJoint
import TwoAxisHelicoid.VerticalRegularity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] complexThetaJet thetaJet

noncomputable def complexThetaQuotient (t : ℂ) (j : ℕ) (v : ℂ) : ℂ :=
  complexThetaJet t j v/complexThetaJet t 0 v

noncomputable def complexG (t a : ℂ) : ℂ :=
  (Real.pi^2/4:ℂ)*(complexThetaQuotient t 1 (Real.pi*a/2)^2-
    complexThetaQuotient t 2 (Real.pi*a/2))-Real.pi/t

noncomputable def complexGa (t a : ℂ) : ℂ :=
  (Real.pi^3/8:ℂ)*(3*complexThetaQuotient t 1 (Real.pi*a/2)*complexThetaQuotient t 2 (Real.pi*a/2)-
    2*complexThetaQuotient t 1 (Real.pi*a/2)^3-complexThetaQuotient t 3 (Real.pi*a/2))

noncomputable def complexGt (t a : ℂ) : ℂ :=
  (Real.pi^3/32:ℂ)*(2*complexThetaQuotient t 1 (Real.pi*a/2)*
    (complexThetaQuotient t 3 (Real.pi*a/2)-complexThetaQuotient t 1 (Real.pi*a/2)*
      complexThetaQuotient t 2 (Real.pi*a/2))-
    (complexThetaQuotient t 4 (Real.pi*a/2)-complexThetaQuotient t 2 (Real.pi*a/2)^2))+Real.pi/t^2

theorem complexThetaQuotient_ofReal (t : ℝ) (j : ℕ) (v : ℂ) :
    complexThetaQuotient t j v = thetaQuotient t j v := by
  simp only [complexThetaQuotient,thetaQuotient,complexThetaJet_ofReal]

theorem complexG_ofReal (t a : ℝ) : complexG t a = thetaG t a := by
  simp only [complexG,thetaG,complexThetaQuotient_ofReal]
  push_cast
  rfl

theorem complexGa_ofReal (t a : ℝ) : complexGa t a = thetaGa t a := by
  simp only [complexGa,thetaGa,complexThetaQuotient_ofReal]

theorem complexThetaQuotient_space_hasDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ)
    (hv : complexThetaJet t 0 v ≠ 0) :
    HasDerivAt (complexThetaQuotient t j)
      (complexThetaQuotient t (j+1) v-complexThetaQuotient t j v*complexThetaQuotient t 1 v) v := by
  have hd := (complexThetaJet_space_hasDerivAt ht j v).div (complexThetaJet_space_hasDerivAt ht 0 v) hv
  convert hd using 1
  · rfl
  · simp only [complexThetaQuotient]
    field_simp

theorem complexThetaQuotient_time_hasDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (v : ℂ)
    (hv : complexThetaJet t 0 v ≠ 0) :
    HasDerivAt (fun s : ℂ => complexThetaQuotient s j v)
      ((Real.pi/8:ℂ)*(complexThetaQuotient t (j+2) v-
        complexThetaQuotient t j v*complexThetaQuotient t 2 v)) t := by
  have hd := (complexThetaJet_time_hasDerivAt ht j v).div (complexThetaJet_time_hasDerivAt ht 0 v) hv
  convert hd using 1
  · rfl
  · simp only [complexThetaQuotient]
    field_simp
    ring

theorem complexThetaQuotient_a_hasDerivAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (a : ℂ)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (fun b : ℂ => complexThetaQuotient t j (Real.pi*b/2))
      ((Real.pi/2:ℂ)*(complexThetaQuotient t (j+1) (Real.pi*a/2)-
        complexThetaQuotient t j (Real.pi*a/2)*complexThetaQuotient t 1 (Real.pi*a/2))) a := by
  have harg := ((hasDerivAt_id a).const_mul (Real.pi:ℂ)).div_const 2
  have hd := (complexThetaQuotient_space_hasDerivAt ht j _ ha).comp a harg
  convert hd using 1
  · rfl
  · simp only [mul_one]
    ring

theorem complexG_a_hasDerivAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (complexG t) (complexGa t a) a := by
  have h1 := complexThetaQuotient_a_hasDerivAt ht 1 a ha
  have h2 := complexThetaQuotient_a_hasDerivAt ht 2 a ha
  have hd := (((h1.pow 2).sub h2).const_mul (Real.pi^2/4:ℂ)).sub_const (Real.pi/t)
  convert hd using 1
  · rfl
  · simp only [complexGa]
    norm_num
    ring

theorem complexG_t_hasDerivAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasDerivAt (fun s => complexG s a) (complexGt t a) t := by
  have htne : t ≠ 0 := by intro he; simp only [he,Complex.zero_re] at ht; exact lt_irrefl _ ht
  have h1 := complexThetaQuotient_time_hasDerivAt ht 1 (Real.pi*a/2) ha
  have h2 := complexThetaQuotient_time_hasDerivAt ht 2 (Real.pi*a/2) ha
  have hp := (hasDerivAt_const t (Real.pi:ℂ)).div (hasDerivAt_id t) htne
  have hd := (((h1.pow 2).sub h2).const_mul (Real.pi^2/4:ℂ)).sub hp
  convert hd using 1
  · rfl
  · simp only [complexGt]
    norm_num
    ring

theorem complexThetaJet_abscissa_continuousAt {t : ℂ} (ht : 0 < t.re) (j : ℕ) (a : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => complexThetaJet p.1 j (Real.pi*p.2/2)) (t,a) := by
  have hp : ContinuousAt (fun p : ℂ × ℂ => (p.1,Real.pi*p.2/2)) (t,a) := by fun_prop
  have h := (complexThetaJet_joint_continuousAt ht j (Real.pi*a/2)).comp
    (f := fun p : ℂ × ℂ => (p.1,Real.pi*p.2/2)) (x := (t,a)) hp
  exact h

theorem complexThetaQuotient_abscissa_continuousAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) (j : ℕ) :
    ContinuousAt (fun p : ℂ × ℂ => complexThetaQuotient p.1 j (Real.pi*p.2/2)) (t,a) := by
  unfold complexThetaQuotient
  exact (complexThetaJet_abscissa_continuousAt ht j a).div
    (complexThetaJet_abscissa_continuousAt ht 0 a) ha

theorem complexGa_joint_continuousAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => complexGa p.1 p.2) (t,a) := by
  have h1 := complexThetaQuotient_abscissa_continuousAt ht ha 1
  have h2 := complexThetaQuotient_abscissa_continuousAt ht ha 2
  have h3 := complexThetaQuotient_abscissa_continuousAt ht ha 3
  exact continuousAt_const.mul ((((continuousAt_const.mul h1).mul h2).sub
    (continuousAt_const.mul (h1.pow 3))).sub h3)

theorem complexGt_joint_continuousAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => complexGt p.1 p.2) (t,a) := by
  have htne : t ≠ 0 := by intro he; simp only [he,Complex.zero_re] at ht; exact lt_irrefl _ ht
  have h1 := complexThetaQuotient_abscissa_continuousAt ht ha 1
  have h2 := complexThetaQuotient_abscissa_continuousAt ht ha 2
  have h3 := complexThetaQuotient_abscissa_continuousAt ht ha 3
  have h4 := complexThetaQuotient_abscissa_continuousAt ht ha 4
  have hp : ContinuousAt (fun p : ℂ × ℂ => (Real.pi:ℂ)/p.1^2) (t,a) :=
    continuousAt_const.div (continuous_fst.continuousAt.pow 2) (pow_ne_zero 2 htne)
  exact (continuousAt_const.mul (((continuousAt_const.mul h1).mul (h3.sub (h1.mul h2))).sub
    (h4.sub (h2.pow 2)))).add hp

noncomputable def complexGDeriv (t a : ℂ) : ℂ × ℂ →L[ℂ] ℂ :=
  ((1:ℂ →L[ℂ] ℂ).smulRight (complexGt t a)).coprod ((1:ℂ →L[ℂ] ℂ).smulRight (complexGa t a))

theorem complexG_joint_hasStrictFDerivAt {t a : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasStrictFDerivAt (fun p : ℂ × ℂ => complexG p.1 p.2) (complexGDeriv t a) (t,a) := by
  have hp : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,a), 0 < p.1.re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds ht
  have hn : ∀ᶠ p : ℂ × ℂ in 𝓝 (t,a), complexThetaJet p.1 0 (Real.pi*p.2/2) ≠ 0 :=
    (complexThetaJet_abscissa_continuousAt ht 0 a).eventually_ne ha
  apply hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℂ) (u := (t,a)) (f := complexG)
    (f₁ := fun t a => (1:ℂ →L[ℂ] ℂ).smulRight (complexGt t a))
    (f₂ := fun t a => (1:ℂ →L[ℂ] ℂ).smulRight (complexGa t a))
  · filter_upwards [hp,hn] with p hp hn
    exact (complexG_t_hasDerivAt hp hn).hasFDerivAt
  · filter_upwards [hp,hn] with p hp hn
    exact (complexG_a_hasDerivAt hp hn).hasFDerivAt
  · exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => complexGt p.1 p.2) (complexGt_joint_continuousAt ht ha)
  · exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.continuousAt.comp
      (f := fun p : ℂ × ℂ => complexGa p.1 p.2) (complexGa_joint_continuousAt ht ha)

theorem complexGDeriv_inr_invertible {t a : ℂ} (ha : complexGa t a ≠ 0) :
    (complexGDeriv t a ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ ha),?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp [complexGDeriv,ContinuousLinearEquiv.unitsEquivAut_apply]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexG_joint_hasStrictFDerivAt
