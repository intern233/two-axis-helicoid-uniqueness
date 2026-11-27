import TwoAxisHelicoid.SmoothImmersionLeftInverse
import TwoAxisHelicoid.MeridianLiftMarkedTorus
import TwoAxisHelicoid.PuncturedMarkedTangentFrame
import TwoAxisHelicoid.CompressingDiskTorusParity

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Manifold ContDiff

/-- The meridional inward radial derivative in a genuine regular
three-dimensional product chart is transverse to every two-plane
containing its actual longitudinal and meridional angular derivatives. -/
theorem meridian_radial_transverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : (ℝ × ℂ) →L[ℝ] V) (A : ℂ →L[ℝ] V)
    (hD : Function.Injective D) (hA : Function.Injective A) {z : ℂ} (hz : z ≠ 0)
    (hθ : D (1,0) ∈ LinearMap.range A.toLinearMap) (hφ : D (0,I*z) ∈ LinearMap.range A.toLinearMap) :
    D (0,I*(I*z)) ∉ LinearMap.range A.toLinearMap := by
  intro hrad
  let K := LinearMap.range A.toLinearMap
  have hzr : D (0,-z) ∈ K := by simpa only [← mul_assoc,I_mul_I,neg_one_mul] using hrad
  have hzp : D (0,z) ∈ K := by
    have he : ((0:ℝ),z) = -(0,-z) := by simp
    rw [he,map_neg]
    exact K.neg_mem hzr
  have hall : LinearMap.range D.toLinearMap ≤ K := by
    rintro v ⟨⟨a,b⟩,rfl⟩
    let c := b/z
    have he : c.re • z + c.im • (I*z) = b := by
      rw [Complex.real_smul,Complex.real_smul,← mul_assoc,← add_mul,Complex.re_add_im]
      exact div_mul_cancel₀ b hz
    have hp : (a,b) = a • (1,0) + c.re • (0,z) + c.im • (0,I*z) := by
      apply Prod.ext
      · simp
      · simpa using he.symm
    change D (a,b) ∈ K
    rw [hp,map_add,map_add,map_smul,map_smul,map_smul]
    exact K.add_mem (K.add_mem (K.smul_mem a hθ) (K.smul_mem _ hzp)) (K.smul_mem _ hφ)
  have hdim := Submodule.finrank_mono hall
  rw [LinearMap.finrank_range_of_inj (f := D.toLinearMap) hD,
    LinearMap.finrank_range_of_inj (f := A.toLinearMap) hA,Module.finrank_prod,
    Complex.finrank_real_complex,Module.finrank_self] at hdim
  omega

/-- A smooth spatial curve known to lie in an immersed marked surface
has velocity in its actual tangent plane. A continuous local marking
of the curve suffices. -/
theorem derivative_mem_plane_of_lift {Y : ℂ → Fin 3 → ℝ} {v : ℝ → ℂ} {g : ℝ → Fin 3 → ℝ}
    {s : ℝ} (hY : ContDiffAt ℝ ∞ Y (v s)) (hi : Function.Injective (fderiv ℝ Y (v s)))
    (hv : ContinuousAt v s) (hg : ContDiffAt ℝ ∞ g s) (h : Y ∘ v =ᶠ[nhds s] g) :
    deriv g s ∈ LinearMap.range (fderiv ℝ Y (v s)).toLinearMap := by
  have hc := contDiffAt_of_comp_immersion hY hi hv (hg.congr_of_eventuallyEq h)
  have hd := (hY.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
    (hc.differentiableAt (by simp)).hasDerivAt
  exact ⟨deriv v s,(hd.congr_of_eventuallyEq h.symm).deriv.symm⟩

/-- Tangency to the surface in a product meridian follows by lifting
a smooth boundary curve to the actual marking through any prescribed
parameter value. The surface only needs to be regular at that point. -/
theorem spatial_torus_curve_derivative_mem (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (β : C(ℝ,PeriodTorus L)) {t : ℝ} {z : ℂ}
    (hz : periodTorusProjection L z = β t)
    (hY : ContDiffAt ℝ ∞ (F ∘ periodTorusProjection L) z)
    (hi : Function.Injective (fderiv ℝ (F ∘ periodTorusProjection L) z))
    {g : ℝ → Fin 3 → ℝ} (hg : ContDiffAt ℝ ∞ g t) (h : (fun r => F (β r)) =ᶠ[nhds t] g) :
    deriv g t ∈ LinearMap.range (fderiv ℝ (F ∘ periodTorusProjection L) z).toLinearMap := by
  obtain ⟨v,⟨hv,hp⟩,_⟩ := (periodTorusProjection_isCoveringMap L).existsUnique_continuousMap_lifts β t z hz
  have h' : (F ∘ periodTorusProjection L) ∘ v =ᶠ[nhds t] g := by
    filter_upwards [h] with r hr
    exact (congrArg F (congrFun hp r)).trans hr
  have he := derivative_mem_plane_of_lift (s := t) (Y := F ∘ periodTorusProjection L) (v := v) (g := g)
    (hv.symm ▸ hY) (hv.symm ▸ hi) v.continuous.continuousAt hg h'
  rwa [hv] at he

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.meridian_radial_transverse
#print axioms TwoAxisHelicoid.spatial_torus_curve_derivative_mem
