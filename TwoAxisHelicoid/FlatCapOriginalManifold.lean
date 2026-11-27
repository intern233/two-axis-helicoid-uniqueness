import TwoAxisHelicoid.RegularCapChart
import TwoAxisHelicoid.CommonImmersionSmoothStructures
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

variable {M E A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [ChartedSpace E M]

theorem manifold_to_normed_chart_derivative {F : M → A} {x : M}
    (hF : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x =
      fderiv ℝ (F ∘ (chartAt E x).symm) (chartAt E x x) := by
  have hc : ContDiffAt ℝ ∞ (F ∘ (chartAt E x).symm) (chartAt E x x) := by
    simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp hF).2
  have hd : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,A) F x
      (fderiv ℝ (F ∘ (chartAt E x).symm) (chartAt E x x)) := by
    refine ⟨hF.continuousAt,?_⟩
    simpa only [writtenInExtChartAt,mfld_simps] using!
      (hc.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt (s := range 𝓘(ℝ,E))
  exact hd.mfderiv

/-- The cap is also a genuine smooth immersion in the original manifold
structure at every point other than the added point. -/
theorem actual_flat_cap_original_manifold_regular [T1Space M]
    {X F : M → HelicoidTubeCoordinates} {p x : M} (hxp : x ≠ p)
    (hX : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ X x)
    (hXi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,HelicoidTubeCoordinates) X x))
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hF : ∀ q ≠ p, F q = ambientPlaneCap A H (X q))
    (hflat : ∀ q ≠ p, R^2 < ambientRadiusSq (X q) → (X q).1.2 = 0) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F x ∧
      Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,HelicoidTubeCoordinates) F x) := by
  have heq : F =ᶠ[𝓝 x] ambientPlaneCap A H ∘ X := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hxp] with q hq
    exact hF q hq
  have hsm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F x :=
    (((ambientPlaneCap_contDiff A H).contMDiff.contMDiffAt).comp x hX).congr_of_eventuallyEq heq
  refine ⟨hsm,?_⟩
  let e := chartAt E x
  let y := e x
  have hx : x ∈ e.source := mem_chart_source E x
  have hy : y ∈ e.target := e.map_source hx
  have hc : ContinuousAt e.symm y := e.continuousAt_symm hy
  have hne : ∀ᶠ z in 𝓝 y, e.symm z ≠ p := by
    have hp : ∀ᶠ q in 𝓝 (e.symm y), q ≠ p := by
      change ({p}ᶜ : Set M) ∈ 𝓝 (e.symm y)
      rw [e.left_inv hx]
      exact isOpen_compl_singleton.mem_nhds hxp
    exact hc.eventually hp
  have heq' : F ∘ e.symm =ᶠ[𝓝 y] ambientPlaneCap A H ∘ (X ∘ e.symm) := by
    filter_upwards [hne] with z hz
    exact hF (e.symm z) hz
  have hxc : ContDiffAt ℝ ∞ (X ∘ e.symm) y := by
    simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp hX).2
  have hdi : Function.Injective (fderiv ℝ (X ∘ e.symm) y) := by
    rw [manifold_to_normed_chart_derivative hX] at hXi
    exact hXi
  rw [manifold_to_normed_chart_derivative hsm]
  change Function.Injective (fderiv ℝ (F ∘ e.symm) y)
  rw [heq'.fderiv_eq]
  apply ambientPlaneCap_preserves_local_immersion (hxc.differentiableAt (by simp)) hdi hR hA1 hAR hH
  filter_upwards [hne] with z hz
  exact hflat (e.symm z) hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manifold_to_normed_chart_derivative
#print axioms TwoAxisHelicoid.actual_flat_cap_original_manifold_regular
