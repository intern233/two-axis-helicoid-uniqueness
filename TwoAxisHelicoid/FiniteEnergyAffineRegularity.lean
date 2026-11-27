import TwoAxisHelicoid.PlaneConductivityTranslationBounds

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem planeAffineFluxLoad_smooth {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) :
    ContDiff ℝ ∞ (planeAffineFluxLoad A B C) := by
  apply contDiff_const.sub
  change ContDiff ℝ ∞ (Complex.equivRealProdCLM.symm ∘ (fun z : ℂ =>
    (C z*(1:ℂ).re-B z*(1:ℂ).im,A z*(1:ℂ).im-B z*(1:ℂ).re)))
  apply Complex.equivRealProdCLM.symm.contDiff.comp
  apply ContDiff.prodMk <;> fun_prop (disch := assumption)

private theorem true_flux {A B C : ℂ → ℝ}
    (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ))
    (b u : Lp ℂ 2 (volume:Measure ℂ)) (acts : ∀ w, ⇑(T w) =ᵐ[volume] (fun z => planeMetricFlux A B C z (w z)))
    (rep : ⇑b =ᵐ[volume] planeAffineFluxLoad A B C)
    (orth : ∀ w∈planeDirichletGradients volume univ, ⟪T u-b,w⟫_ℝ=0)
    {φ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ) :
    (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ)=0 := by
  let m := planeTestGradient_memLp (μ:=volume) s h
  let w := m.toLp (planeTestGradient φ)
  have hw : w∈planeDirichletGradients volume univ :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ,s,h,subset_univ _,m.coeFn_toLp⟩)
  have q : ∀ᵐ z : ℂ, planeMetricFlux A B C z (1+u z)=(T u-b) z+1 := by
    filter_upwards [Lp.coeFn_sub (T u) b,acts u,rep] with z hz ht hb
    rw [hz,Pi.sub_apply,ht,hb]
    apply Complex.ext <;> simp [planeMetricFlux,planeAffineFluxLoad] <;> ring
  have eq : (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ)=
      (∫ z, ⟪(T u-b) z,w z⟫_ℝ + fderiv ℝ φ z 1) := by
    apply integral_congr_ae
    filter_upwards [q,m.coeFn_toLp] with z hq hwv
    rw [hq,hwv,inner_add_left,real_inner_comm (planeTestGradient φ z) (1:ℂ),planeTestGradient_pair]
  have dc := (s.continuous_fderiv (by simp)).clm_apply (continuous_const (y:=(1:ℂ)))
  rw [eq,integral_add (L2.integrable_inner (𝕜:=ℝ) (T u-b) w) (dc.integrable_of_hasCompactSupport (h.fderiv_apply ℝ 1)),
    ← L2.inner_def,orth w hw,plane_compact_derivative_integral_zero s h,add_zero]

/-- The full-plane affine solution has finite correction energy and bounded
first translation differences in the actual L² norm, in every direction.
Its original divergence equation holds for all compact scalar tests. -/
theorem exists_finite_energy_affine_with_translation_bound {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1) {K : Set ℂ} (hk : IsCompact K)
    (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ u ∈ planeDirichletGradients volume univ, ∃ D : ℝ, 0≤D ∧
      (∀ t : ℂ, ‖t‖≤1 → ‖planeFieldTranslate t u-u‖≤D*‖t‖) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ)=0 := by
  obtain ⟨k,T,b,k1,acts,lower,rep,u,solution,_⟩ :=
    exists_whole_plane_affine_corrector sa.continuous sb.continuous sc.continuous ha det hk off
  have orth (w : Lp ℂ 2 (volume:Measure ℂ)) (hw : w∈planeDirichletGradients volume univ) :
      ⟪T u.val-b,w⟫_ℝ=0 := solution ⟨w,hw⟩
  obtain ⟨L,l0,comm⟩ := smooth_conductivity_translation_commutator sa sb sc hk off T acts
  obtain ⟨_,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (planeAffineFluxLoad_compact hk off)
    (planeAffineFluxLoad_smooth sa sb sc) (by simp)
  obtain ⟨M,m0,load⟩ := compact_load_translation_estimate (planeAffineFluxLoad_compact hk off) lip b rep
  have kp : 0<k := by linarith
  refine ⟨u.val,u.2,k*(L*‖u.val‖+M),by positivity,?_,fun _ s h => true_flux T b u.val acts rep orth s h⟩
  intro t ht
  have energy := whole_plane_gradient_translation_energy T lower u.val b u.2 orth t
  have upper := energy.trans (add_le_add (comm t u.val) (load t ht))
  calc
    _ = k*(k⁻¹*‖planeFieldTranslate t u.val-u.val‖) := by field_simp
    _ ≤ k*(L*‖t‖*‖u.val‖+M*‖t‖) := mul_le_mul_of_nonneg_left upper kp.le
    _ = _ := by ring
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_finite_energy_affine_with_translation_bound
