import TwoAxisHelicoid.SolidTorusMeridianTransverse

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Manifold ContDiff

theorem spinCircleParameter_contDiff : ContDiff ℝ ∞ spinCircleParameter := by
  change ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*I))
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const).cexp

/-- A boundary meridian, parametrized by an actual regular solid-cylinder
chart on an open longitudinal interval, supplies all the data for the
compressing disk criterion. Tangency, transversality, smoothness and the
nonzero integer displacement are conclusions. -/
theorem solid_torus_meridian_disk_data (L : PeriodPair) {F : PeriodTorus L → Fin 3 → ℝ}
    (hs : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (H : Circle × Circle ≃ₜ PeriodTorus L) (a : Circle) (ha : ∀ u, H (a,u) ≠ 0)
    (E : ℝ × ℂ → Fin 3 → ℝ) (hE : ∀ z ∈ closedBall (0:ℂ) 1, ContDiffAt ℝ ∞ E (0,z))
    (hEi : ∀ z ∈ closedBall (0:ℂ) 1, Function.Injective (fderiv ℝ E (0,z)))
    {δ : ℝ} (hδ : 0 < δ) (hbd : ∀ s ∈ Ioo (-δ) δ, ∀ u : Circle, F (H (Circle.exp s*a,u)) = E (s,(u:ℂ))) :
    let G := fun z : ℂ => E (0,z)
    ∃ (ξ : ℝ → ℂ) (period : ℂ), ContDiff ℝ 1 ξ ∧ (∀ t, ξ t ∉ L.lattice) ∧ period ≠ 0 ∧ period ∈ L.lattice ∧
      (∀ t, ξ (t+1) = ξ t+period) ∧ (∀ t, deriv ξ t ≠ 0) ∧
      (∀ t h : ℝ, h ∈ Ioo (0:ℝ) 1 → ξ (t+h) ≠ ξ t) ∧
      (∀ z ∈ closedBall (0:ℂ) 1, DifferentiableAt ℝ G z) ∧ ContinuousOn (fderiv ℝ G) (closedBall 0 1) ∧
      (∀ z ∈ closedBall (0:ℂ) 1, Function.Injective (fderiv ℝ G z)) ∧
      (∀ t, F (periodTorusProjection L (ξ t)) = G (spinCircleParameter t)) ∧
      ∀ t : unitInterval, fderiv ℝ G (spinDiskBoundary t) (I*(I*spinDiskBoundary t)) ∉
        LinearMap.range (fderiv ℝ (F ∘ periodTorusProjection L) (ξ t.1)).toLinearMap := by
  let J : ℂ →L[ℝ] (ℝ × ℂ) := (0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)
  let G := fun z : ℂ => E (0,z)
  let k := 2*Real.pi
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let c (t : ℝ) := Circle.exp (k*t)
  have hcb (t : ℝ) : spinCircleParameter t ∈ closedBall (0:ℂ) 1 := by
    change ((c t : Circle) : ℂ) ∈ closedBall (0:ℂ) 1
    simpa only [mem_closedBall,dist_zero_right,Circle.norm_coe] using (le_refl (1:ℝ))
  have hcn (t : ℝ) : spinCircleParameter t ≠ 0 := (c t).coe_ne_zero
  have hGs (z : ℂ) (hz : z ∈ closedBall (0:ℂ) 1) : ContDiffAt ℝ ∞ G z := (hE z hz).comp z J.contDiff.contDiffAt
  have hGD (z : ℂ) (hz : z ∈ closedBall (0:ℂ) 1) : fderiv ℝ G z = (fderiv ℝ E (0,z)).comp J :=
    (((hE z hz).differentiableAt (by simp)).hasFDerivAt.comp z J.hasFDerivAt).fderiv
  have hGi (z : ℂ) (hz : z ∈ closedBall (0:ℂ) 1) : Function.Injective (fderiv ℝ G z) := by
    rw [hGD z hz]
    exact (hEi z hz).comp fun x y h => congrArg Prod.snd h
  obtain ⟨ξ,period,hω,hωL,hπ,hper,hxi⟩ := marked_boundary_torus_meridian_lift L H a
  let Y := F ∘ periodTorusProjection L
  have hx (t : ℝ) : ξ t ∉ L.lattice := by
    intro ht
    exact ha (c t) ((hπ t).symm.trans ((periodTorusProjection_eq_zero L _).mpr ht))
  have hY (t : ℝ) := spatial_torus_lift_regular_at L F (hx t) hs hi
  have hbody (t : ℝ) : Y (ξ t) = G (spinCircleParameter t) := by
    change F (periodTorusProjection L (ξ t)) = E (0,(c t : ℂ))
    rw [hπ]
    simpa only [Circle.exp_zero,one_mul] using hbd 0 ⟨neg_lt_zero.mpr hδ,hδ⟩ (c t)
  have hcurve (t : ℝ) : ContDiffAt ℝ ∞ (G ∘ spinCircleParameter) t :=
    (hGs _ (hcb t)).comp t spinCircleParameter_contDiff.contDiffAt
  have hξ (t : ℝ) : ContDiffAt ℝ ∞ ξ t := contDiffAt_of_comp_immersion (hY t).1 (hY t).2 ξ.continuous.continuousAt
    (by rw [show Y ∘ ξ = G ∘ spinCircleParameter from funext hbody]; exact hcurve t)
  have hvel (t : ℝ) : fderiv ℝ Y (ξ t) (deriv ξ t) = k • (fderiv ℝ G (spinCircleParameter t) (I*spinCircleParameter t)) := by
    have hy := ((hY t).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t ((hξ t).differentiableAt (by simp)).hasDerivAt
    have hg := ((hGs _ (hcb t)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (spinCircleParameter_hasDerivAt t)
    simpa only [map_smul] using (hy.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hbody s).symm)).unique hg
  have hr (t : ℝ) : deriv ξ t ≠ 0 := by
    intro hv
    have h := hvel t
    rw [hv,map_zero] at h
    have he := (smul_eq_zero.mp h.symm).resolve_left hk
    exact (mul_ne_zero I_ne_zero (hcn t)) ((hGi _ (hcb t)) (he.trans (map_zero _).symm))
  refine ⟨ξ,period,(contDiff_iff_contDiffAt.mpr hξ).of_le (by simp),hx,hω,hωL,hper,hr,?_,
    fun z hz => (hGs z hz).differentiableAt (by simp),fun z hz => ((hGs z hz).continuousAt_fderiv (by simp)).continuousWithinAt,
    hGi,hbody,?_⟩
  · intro t s hs h
    have ht := hxi h
    linarith [hs.1]
  intro t
  let z := spinCircleParameter t.1
  let D := fderiv ℝ E (0,z)
  let A := fderiv ℝ Y (ξ t.1)
  let β : C(ℝ,PeriodTorus L) := ⟨fun s => H (Circle.exp s*a,c t.1),
    H.continuous.comp ((Circle.exp.continuous.mul continuous_const).prodMk continuous_const)⟩
  have hβ : periodTorusProjection L (ξ t.1) = β 0 := by simpa [β,c,k] using hπ t.1
  have heq : (fun s => F (β s)) =ᶠ[nhds 0] (fun s => E (s,z)) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    exact hbd s hs (c t.1)
  have hpath : ContDiffAt ℝ ∞ (fun s : ℝ => E (s,z)) 0 :=
    (hE z (hcb t.1)).comp (f := fun s : ℝ => (s,z)) 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hlong : D (1,0) ∈ LinearMap.range A.toLinearMap := by
    have h := spatial_torus_curve_derivative_mem L F β hβ (hY t.1).1 (hY t.1).2 hpath heq
    have hd := ((hE z (hcb t.1)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
    exact hd.deriv ▸ h
  have hmer : D (0,I*z) ∈ LinearMap.range A.toLinearMap := by
    have hv := hvel t.1
    rw [hGD _ (hcb t.1)] at hv
    change A (deriv ξ t.1) = k • D (0,I*z) at hv
    refine ⟨k⁻¹ • deriv ξ t.1,?_⟩
    change A (k⁻¹ • deriv ξ t.1) = D (0,I*z)
    rw [map_smul,hv,inv_smul_smul₀ hk]
  change fderiv ℝ G z (I*(I*z)) ∉ LinearMap.range A.toLinearMap
  rw [hGD z (hcb t.1)]
  exact meridian_radial_transverse D A (hEi _ (hcb t.1)) (hY t.1).2 (hcn t.1) hlong hmer

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.solid_torus_meridian_disk_data
