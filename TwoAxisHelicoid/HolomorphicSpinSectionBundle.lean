import TwoAxisHelicoid.MultiplierAnalyticBundle
import TwoAxisHelicoid.MultiplierCanonicalSquare
import TwoAxisHelicoid.HolomorphicMultiplierParity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bundle
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

abbrev MultiplierAnalyticSection :=
  ContMDiffSection 𝓘(ℂ) ℂ ω (analyticMultiplierBundleCore L χ).Fiber

noncomputable def multiplierBundleSectionMap (S : MultiplierLineSection L χ) :
    PeriodTorus L → (analyticMultiplierBundleCore L χ).TotalSpace :=
  fun q => ⟨q,multiplierBundleFiberEquiv L χ q (S q)⟩

theorem multiplierBundleSectionMap_analyticAt_iff (S : MultiplierLineSection L χ) (q : PeriodTorus L) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (multiplierBundleSectionMap L χ S) q ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun b => multiplierSectionPlane L χ S (multiplierChartLift L q b)) q := by
  change ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun b => TotalSpace.mk' ℂ b (multiplierBundleFiberEquiv L χ b (S b))) q ↔ _
  rw [Bundle.contMDiffAt_section]
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun b => ((analyticMultiplierBundleCore L χ).localTriv q
    ⟨b,multiplierBundleFiberEquiv L χ b (S b)⟩).2) q ↔ _
  simp only [analyticMultiplierBundle_local_section]

/-- The scalar equation used to count sections is equivalent to
complex analyticity of the section of the standard mathlib vector bundle. -/
theorem multiplierBundleSectionMap_analytic_iff (S : MultiplierLineSection L χ) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (multiplierBundleSectionMap L χ S) ↔
      S ∈ holomorphicMultiplierSections L χ := by
  change _ ↔ Differentiable ℂ (multiplierSectionPlane L χ S)
  constructor
  · intro h z
    let q := periodTorusProjection L z
    let f := multiplierSectionPlane L χ S
    obtain ⟨v,hv⟩ := period_torus_projection_chart_translate L z
    have hc := ((multiplierBundleSectionMap_analyticAt_iff L χ S q).mp (h q)).comp
      z (period_torus_projection_complex_analytic L z)
    let k := paritySign (χ v)
    have hπ : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
    have hchart := hπ.continuousAt.eventually (multiplierChartLift_on_chart L (mem_chart_source ℂ q))
    have he : (fun w => k*f w) =ᶠ[𝓝 z] fun w => f (multiplierChartLift L q (periodTorusProjection L w)) := by
      filter_upwards [hv,hchart] with w hw hw'
      rw [hw',hw]
      exact (multiplierSectionPlane_translate L χ S w v).symm
    have hsc : ContDiffAt ℂ ω (fun w => k*f w) z :=
      (contMDiffAt_iff_contDiffAt.mp hc).congr_of_eventuallyEq he
    have hk : k*k = 1 := by simpa only [sq] using paritySign_sq (χ v)
    have H := (hsc.differentiableAt (by simp)).const_mul k
    simpa only [← mul_assoc,hk,one_mul] using H
  · intro hf q
    apply (multiplierBundleSectionMap_analyticAt_iff L χ S q).mpr
    have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ q) q := by
      simpa only [mfld_simps] using! (contMDiffAt_extChartAt (I := 𝓘(ℂ)) (x := q) (n := ω))
    have h := (hf.analyticAt (chartAt ℂ q q)).contDiffAt.contMDiffAt.comp q hchart
    apply h.congr_of_eventuallyEq
    filter_upwards [multiplierChartLift_on_chart L (mem_chart_source ℂ q)] with b hb
    exact congrArg (multiplierSectionPlane L χ S) hb

/-- The odd-fiber representation gives exactly the usual space of
global complex analytic sections, with its standard complex module. -/
noncomputable def holomorphicMultiplierSectionBundleEquiv :
    holomorphicMultiplierSections L χ ≃ₗ[ℂ] MultiplierAnalyticSection L χ where
  toFun s := ⟨fun b => multiplierBundleFiberEquiv L χ b (s.1 b),
    (multiplierBundleSectionMap_analytic_iff L χ s.1).mpr s.2⟩
  invFun t := ⟨fun b => (multiplierBundleFiberEquiv L χ b).symm (t b),by
    apply (multiplierBundleSectionMap_analytic_iff L χ _).mp
    change ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun b => TotalSpace.mk' ℂ b
      (multiplierBundleFiberEquiv L χ b ((multiplierBundleFiberEquiv L χ b).symm (t b))))
    simp only [LinearEquiv.apply_symm_apply]
    exact t.contMDiff⟩
  left_inv s := Subtype.ext (funext fun b => (multiplierBundleFiberEquiv L χ b).symm_apply_apply _)
  right_inv t := ContMDiffSection.ext fun b => (multiplierBundleFiberEquiv L χ b).apply_symm_apply _
  map_add' s t := ContMDiffSection.ext fun b => map_add (multiplierBundleFiberEquiv L χ b) _ _
  map_smul' c s := ContMDiffSection.ext fun b => map_smul (multiplierBundleFiberEquiv L χ b) _ _

/-- The geometric genus-one spin-line section dimension is computed in
the library's bundled analytic-section type. -/
theorem analytic_integer_spin_section_finrank {t : ℝ} (ht : 0 < t) (m : ℤ) :
    Module.finrank ℂ (MultiplierAnalyticSection (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) = if Even m then 1 else 0 := by
  rw [← (holomorphicMultiplierSectionBundleEquiv (rhombicPeriodPair t ht)
    (latticeSpinParity (rhombicPeriodPair t ht) m)).finrank_eq,holomorphicMultiplierSection_finrank ht m]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphicMultiplierSectionBundleEquiv
#print axioms TwoAxisHelicoid.analytic_integer_spin_section_finrank
