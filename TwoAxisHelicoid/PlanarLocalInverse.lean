import TwoAxisHelicoid.StripMapInjective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace TwoAxisHelicoid
open Filter
open scoped Topology

noncomputable def planarLinear (a b c d : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a+
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight c+
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight d)

theorem planarLinear_apply (a b c d : ℝ) (p : ℝ × ℝ) :
    planarLinear a b c d p = (a*p.1+b*p.2,c*p.1+d*p.2) := by
  simp [planarLinear, mul_comm]

noncomputable def planarLinearEquiv (a b c d : ℝ) (hn : a*d-b*c ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toLinearEquiv :=
    { (planarLinear a b c d).toLinearMap with
      invFun := fun p => ((d*p.1-b*p.2)/(a*d-b*c),(-c*p.1+a*p.2)/(a*d-b*c))
      left_inv := by
        intro p
        change (
          (d*(planarLinear a b c d p).1-b*(planarLinear a b c d p).2)/(a*d-b*c),
          (-c*(planarLinear a b c d p).1+a*(planarLinear a b c d p).2)/(a*d-b*c)) = p
        rw [planarLinear_apply]
        apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd]
        · apply (div_eq_iff hn).mpr
          ring
        · apply (div_eq_iff hn).mpr
          ring
      right_inv := by
        intro p
        change planarLinear a b c d ((d*p.1-b*p.2)/(a*d-b*c),(-c*p.1+a*p.2)/(a*d-b*c)) = p
        rw [planarLinear_apply]
        apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd]
        · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          apply (div_eq_iff hn).mpr
          ring
        · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          apply (div_eq_iff hn).mpr
          ring }
  continuous_toFun := (planarLinear a b c d).continuous
  continuous_invFun := by
    change Continuous (fun p : ℝ × ℝ => ((d*p.1-b*p.2)/(a*d-b*c),(-c*p.1+a*p.2)/(a*d-b*c)))
    fun_prop

@[simp] theorem planarLinearEquiv_coe (a b c d : ℝ) (hn : a*d-b*c ≠ 0) :
    (planarLinearEquiv a b c d hn : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = planarLinear a b c d := rfl

theorem scalar_bivariate_hasStrictFDerivAt {F Fs Fr : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hFs : ∀ s r, HasDerivAt (fun t => F t r) (Fs s r) s)
    (hFr : ∀ s r, HasDerivAt (F s) (Fr s r) r)
    (hcFs : Continuous (fun p : ℝ × ℝ => Fs p.1 p.2))
    (hcFr : Continuous (fun p : ℝ × ℝ => Fr p.1 p.2)) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Fs p.1 p.2)+
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Fr p.1 p.2)) p := by
  let D₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s r => (1 : ℝ →L[ℝ] ℝ).smulRight (Fs s r)
  let D₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s r => (1 : ℝ →L[ℝ] ℝ).smulRight (Fr s r)
  have hd1 : ∀ᶠ q : ℝ × ℝ in 𝓝 p, HasFDerivAt (fun t => F t q.2) (D₁ q.1 q.2) q.1 :=
    Eventually.of_forall (fun q => (hFs q.1 q.2).hasFDerivAt)
  have hd2 : ∀ᶠ q : ℝ × ℝ in 𝓝 p, HasFDerivAt (F q.1) (D₂ q.1 q.2) q.2 :=
    Eventually.of_forall (fun q => (hFr q.1 q.2).hasFDerivAt)
  have hc1 : ContinuousAt (fun q : ℝ × ℝ => D₁ q.1 q.2) p :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun q : ℝ × ℝ => Fs q.1 q.2) hcFs.continuousAt
  have hc2 : ContinuousAt (fun q : ℝ × ℝ => D₂ q.1 q.2) p :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp
      (f := fun q : ℝ × ℝ => Fr q.1 q.2) hcFr.continuousAt
  convert! hasStrictFDerivAt_uncurry_coprod (u := p) (f := F) (f₁ := D₁) (f₂ := D₂) hd1 hd2 hc1 hc2 using 1

/-- The ordinary two-dimensional inverse function theorem, with the determinant
condition expressed in scalar partial derivatives. -/
theorem planar_local_inverse {F G Fs Fr Gs Gr : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hFs : ∀ s r, HasDerivAt (fun t => F t r) (Fs s r) s)
    (hFr : ∀ s r, HasDerivAt (F s) (Fr s r) r)
    (hGs : ∀ s r, HasDerivAt (fun t => G t r) (Gs s r) s)
    (hGr : ∀ s r, HasDerivAt (G s) (Gr s r) r)
    (hcFs : Continuous (fun p : ℝ × ℝ => Fs p.1 p.2))
    (hcFr : Continuous (fun p : ℝ × ℝ => Fr p.1 p.2))
    (hcGs : Continuous (fun p : ℝ × ℝ => Gs p.1 p.2))
    (hcGr : Continuous (fun p : ℝ × ℝ => Gr p.1 p.2))
    (hdet : Fs p.1 p.2*Gr p.1 p.2-Fr p.1 p.2*Gs p.1 p.2 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ (e : (ℝ × ℝ) → ℝ × ℝ) = (fun q => (F q.1 q.2,G q.1 q.2)) ∧
      HasStrictFDerivAt e.symm
        ((planarLinearEquiv (Fs p.1 p.2) (Fr p.1 p.2) (Gs p.1 p.2) (Gr p.1 p.2) hdet).symm :
          (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (F p.1 p.2,G p.1 p.2) := by
  let D := planarLinearEquiv (Fs p.1 p.2) (Fr p.1 p.2) (Gs p.1 p.2) (Gr p.1 p.2) hdet
  have hd : HasStrictFDerivAt (fun q : ℝ × ℝ => (F q.1 q.2,G q.1 q.2))
      (D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    (scalar_bivariate_hasStrictFDerivAt hFs hFr hcFs hcFr).prodMk
      (scalar_bivariate_hasStrictFDerivAt hGs hGr hcGs hcGr)
  refine ⟨hd.toOpenPartialHomeomorph _,hd.mem_toOpenPartialHomeomorph_source,rfl,?_⟩
  exact hd.to_localInverse

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planar_local_inverse
