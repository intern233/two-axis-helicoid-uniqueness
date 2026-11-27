import TwoAxisHelicoid.FrozenPlaneVariationalSolution
import TwoAxisHelicoid.ParametricPlaneOrbit
import TwoAxisHelicoid.SmoothLimitGradientPotential

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Metric Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace

/-- At a sufficiently small strictly positive scale, the smooth solution
of the frozen-coefficient interpolation is harmonic for the actual rescaled
coefficients on the unit disk and has nonzero horizontal derivative at 0. -/
theorem exists_rescaled_harmonic_scalar {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (p : ℂ)
    {k : ℝ} (kp : 0<k) (low : ∀ z x y, (x^2+y^2)/k≤C z*x^2-2*B z*x*y+A z*y^2) :
    ∃ (s : ℝ) (v : ℂ → ℝ), 0<s ∧ s<1 ∧ ContDiff ℝ ∞ v ∧ 0<fderiv ℝ v 0 1 ∧
      ∀ z∈ball (0:ℂ) 1,
        fderiv ℝ (fun y => C (p+s • y)*fderiv ℝ v y 1-B (p+s • y)*fderiv ℝ v y I) z 1 =
        fderiv ℝ (fun y => B (p+s • y)*fderiv ℝ v y 1-A (p+s • y)*fderiv ℝ v y I) z I := by
  obtain ⟨u,zero,member,orbit,weak⟩ := exists_frozen_plane_weak_gradients sa sb sc p kp low
  obtain ⟨f,sf,actual⟩ := parametric_smooth_plane_representative u orbit
  have slice (s : ℝ) : ContDiff ℝ ∞ (fun z : ℂ => f (s,z)) := sf.comp (contDiff_const.prodMk contDiff_id)
  have zeroField := actual 0
  rw [zero] at zeroField
  have van : (fun z : ℂ => f (0,z))=0 := Measure.eq_of_ae_eq
    (zeroField.symm.trans (Lp.coeFn_zero ℂ 2 volume)) (slice 0).continuous continuous_const
  have f00 : f (0,0)=0 := congrFun van 0
  have cont : Continuous (fun s : ℝ => (1+f (s,0)).re) := reCLM.continuous.comp
    (continuous_const.add (sf.continuous.comp (continuous_id.prodMk continuous_const)))
  have pos0 : 0<(1+f (0,0)).re := by simp [f00]
  have near : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<(1+f (s,0)).re :=
    (continuousAt_const.eventually_lt (cont.continuousAt (x:=0)) pos0).filter_mono nhdsWithin_le_nhds
  obtain ⟨s,positive,hs⟩ := (near.and (Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num))).exists
  obtain ⟨g,sg,grad⟩ := smooth_representative_gradient_has_potential (u s) (member s) (actual s) (slice s)
  let v := fun z : ℂ => z.re+g z
  have sv : ContDiff ℝ ∞ v := reCLM.contDiff.add sg
  have dv (z : ℂ) : planeTestGradient v z=1+f (s,z) := by
    rw [←grad z]
    have df := (reCLM.hasFDerivAt (x:=z)).add (sg.differentiable (by simp) z).hasFDerivAt
    change planeTestGradient ((reCLM : ℂ→ℝ)+g) z=_
    apply Complex.ext <;> simp [planeTestGradient,df.fderiv]
  refine ⟨s,v,hs.1,hs.2,sv,by change 0<(planeTestGradient v 0).re; rw [dv]; exact positive,?_⟩
  have repr : ∀ᵐ z : ℂ, z∈(univ:Set ℂ) → 1+u s z=planeTestGradient v z := by
    filter_upwards [actual s] with z e
    exact fun _ => (congrArg (fun q : ℂ => 1+q) e).trans (dv z).symm
  have strong := smooth_gradient_of_weak_flux_is_harmonic isOpen_univ (planeFrozenCoefficient_smooth sa p s)
    (planeFrozenCoefficient_smooth sb p s) (planeFrozenCoefficient_smooth sc p s) sv repr
    (fun φ h c _ => weak s φ h c)
  intro z hz
  have core (F : ℂ → ℝ) : (fun y => F (p+s • y)) =ᶠ[𝓝 z] planeFrozenCoefficient F p s := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (planeFrozenCoefficient_core F p (by rw [Real.norm_of_nonneg hs.1.le]; exact hs.2.le)
      (by simpa only [dist_zero_right] using (mem_ball.mp hy).le)).symm
  have xr : (fun y => C (p+s • y)*fderiv ℝ v y 1 - B (p+s • y)*fderiv ℝ v y I) =ᶠ[𝓝 z]
      (fun y => planeFrozenCoefficient C p s y*fderiv ℝ v y 1-planeFrozenCoefficient B p s y*fderiv ℝ v y I) :=
    ((core C).mul EventuallyEq.rfl).sub ((core B).mul EventuallyEq.rfl)
  have yr : (fun y => B (p+s • y)*fderiv ℝ v y 1 - A (p+s • y)*fderiv ℝ v y I) =ᶠ[𝓝 z]
      (fun y => planeFrozenCoefficient B p s y*fderiv ℝ v y 1-planeFrozenCoefficient A p s y*fderiv ℝ v y I) :=
    ((core B).mul EventuallyEq.rfl).sub ((core A).mul EventuallyEq.rfl)
  rw [xr.fderiv_eq,yr.fderiv_eq]
  exact strong z (mem_univ z)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_rescaled_harmonic_scalar
