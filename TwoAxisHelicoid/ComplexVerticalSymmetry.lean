import TwoAxisHelicoid.ComplexVerticalFunction
import TwoAxisHelicoid.ThetaParity

namespace TwoAxisHelicoid
set_option maxRecDepth 10000
open Complex
open scoped ComplexConjugate
attribute [local irreducible] complexThetaJet

theorem complexThetaJet_neg (t : ℂ) (j : ℕ) (v : ℂ) :
    complexThetaJet t j (-v) = (-1:ℂ)^(j+1)*complexThetaJet t j v := by
  have he (n : ℕ) : complexThetaTerm t j n (-v) = (-1:ℂ)^(j+1)*complexThetaTerm t j n v := by
    simp only [complexThetaTerm,mul_neg,sineJet_neg]
    ring
  simp only [complexThetaJet,he,tsum_mul_left]

theorem complexThetaJet_add_pi (t : ℂ) (j : ℕ) (v : ℂ) :
    complexThetaJet t j (v+Real.pi) = -complexThetaJet t j v := by
  have he (n : ℕ) : complexThetaTerm t j n (v+Real.pi) = -complexThetaTerm t j n v := by
    have hh : (2*n+1:ℂ)*(v+Real.pi) = ((2*n+1)*v+n*(2*Real.pi))+Real.pi := by ring
    simp only [complexThetaTerm,hh,sineJet_add_pi,sineJet_add_nat_two_pi]
    ring
  simp only [complexThetaJet,he,tsum_neg]

theorem complexG_reflect (t a : ℂ) : complexG t (2-a) = complexG t a := by
  have he : (Real.pi*(2-a)/2:ℂ) = -(Real.pi*a/2)+Real.pi := by ring
  norm_num [complexG,complexThetaQuotient,he,complexThetaJet_add_pi,complexThetaJet_neg]
  ring

theorem complexThetaJet_conj (t : ℂ) (j : ℕ) (v : ℂ) :
    complexThetaJet (conj t) j (conj v) = conj (complexThetaJet t j v) := by
  have he (n : ℕ) : complexThetaTerm (conj t) j n (conj v) = conj (complexThetaTerm t j n v) := by
    have hs : conj (thetaSign n) = thetaSign n := by unfold thetaSign; split <;> simp
    have hc2 : conj (2:ℂ) = 2 := Complex.conj_ofReal 2
    have hv : (2*n+1:ℂ)*conj v = conj ((2*n+1:ℂ)*v) := by simp [hc2]
    have ht : (-Real.pi*conj t*n*(n+1)/2:ℂ) = conj (-Real.pi*t*n*(n+1)/2) := by simp [hc2]
    unfold complexThetaTerm
    rw [hv,ht,sineJet_conj,Complex.exp_conj]
    simp only [map_mul,hs,map_pow,map_add,map_one,hc2,map_natCast]
  simp only [complexThetaJet,he]
  exact Complex.conjCLE.map_tsum.symm

theorem complexG_conj (t a : ℂ) : complexG (conj t) (conj a) = conj (complexG t a) := by
  have hc2 : conj (2:ℂ) = 2 := Complex.conj_ofReal 2
  have hc4 : conj (4:ℂ) = 4 := Complex.conj_ofReal 4
  have he : (Real.pi*conj a/2:ℂ) = conj (Real.pi*a/2) := by simp [hc2]
  simp only [complexG,complexThetaQuotient,he,complexThetaJet_conj]
  simp only [map_sub,map_mul,map_div₀,map_pow,Complex.conj_ofReal,hc4]

theorem complexGt_ofReal (t a : ℝ) : complexGt t a = thetaGt t a := by
  simp only [complexGt,thetaGt,complexThetaQuotient_ofReal]
  push_cast
  rfl

noncomputable def complexGSwapDeriv (a t : ℂ) : ℂ × ℂ →L[ℂ] ℂ :=
  complexGDeriv t a ∘L ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ))

theorem complexG_swap_hasStrictFDerivAt {a t : ℂ} (ht : 0 < t.re)
    (ha : complexThetaJet t 0 (Real.pi*a/2) ≠ 0) :
    HasStrictFDerivAt (fun p : ℂ × ℂ => complexG p.2 p.1) (complexGSwapDeriv a t) (a,t) := by
  have hs : HasStrictFDerivAt (fun p : ℂ × ℂ => (p.2,p.1))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)) (a,t) :=
    hasStrictFDerivAt_snd.prodMk hasStrictFDerivAt_fst
  exact (complexG_joint_hasStrictFDerivAt ht ha).comp (a,t) hs

theorem complexGSwapDeriv_inr_invertible {a t : ℂ} (ht : complexGt t a ≠ 0) :
    (complexGSwapDeriv a t ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ ht),?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp [complexGSwapDeriv,complexGDeriv,ContinuousLinearEquiv.unitsEquivAut_apply]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complexG_reflect
#print axioms TwoAxisHelicoid.complexG_swap_hasStrictFDerivAt
