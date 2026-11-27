import TwoAxisHelicoid.MultiplierLineSections
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import Mathlib.Geometry.Manifold.VectorBundle.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bundle
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

/-- Each chart supplies local lifts to the plane, extended off the chart
only so that the transition formulas can be total functions. -/
noncomputable def multiplierChartLift (L : PeriodPair) (i b : PeriodTorus L) : ℂ := by
  classical
  exact if b ∈ (chartAt ℂ i).source then chartAt ℂ i b else chartAt ℂ b b

theorem multiplierChartLift_proj (L : PeriodPair) (i b : PeriodTorus L) :
    periodTorusProjection L (multiplierChartLift L i b) = b := by
  classical
  unfold multiplierChartLift
  split_ifs with h
  · rw [← periodTorus_chart_symm_eq_projection L i]
    exact (chartAt ℂ i).left_inv h
  · exact periodTorus_chart_representative L b

theorem multiplierChartLift_on_chart (L : PeriodPair) {i b : PeriodTorus L} (hb : b ∈ (chartAt ℂ i).source) :
    multiplierChartLift L i =ᶠ[𝓝 b] chartAt ℂ i := by
  classical
  filter_upwards [(chartAt ℂ i).open_source.mem_nhds hb] with x hx
  simp [multiplierChartLift,hx]

noncomputable def multiplierChartShift (L : PeriodPair) (i j b : PeriodTorus L) : L.lattice :=
  ⟨multiplierChartLift L j b-multiplierChartLift L i b,QuotientAddGroup.eq_iff_sub_mem.mp
    ((multiplierChartLift_proj L j b).trans (multiplierChartLift_proj L i b).symm)⟩

theorem multiplierChartShift_constant (L : PeriodPair) {i j b : PeriodTorus L}
    (hb : b ∈ (chartAt ℂ i).source ∩ (chartAt ℂ j).source) :
    ∀ᶠ x in 𝓝 b, multiplierChartShift L i j x = multiplierChartShift L i j b := by
  have hcont (v : PeriodTorus L) (hv : b ∈ (chartAt ℂ v).source) : ContinuousAt (multiplierChartLift L v) b :=
    ((chartAt ℂ v).continuousAt hv).congr_of_eventuallyEq (multiplierChartLift_on_chart L hv)
  have hs : ContinuousAt (multiplierChartShift L i j) b := IsInducing.subtypeVal.continuousAt_iff.mpr ((hcont j hb.2).sub (hcont i hb.1))
  exact hs.eventually (isOpen_discrete ({multiplierChartShift L i j b} : Set L.lattice) |>.mem_nhds rfl)

noncomputable def multiplierChartTransition (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (i j b : PeriodTorus L) : ℂ →L[ℂ] ℂ :=
  paritySign (χ (multiplierChartShift L i j b)) • ContinuousLinearMap.id ℂ ℂ

theorem multiplierChartTransition_eventually (L : PeriodPair) (χ : L.lattice →+ ZMod 2) {i j b : PeriodTorus L}
    (hb : b ∈ (chartAt ℂ i).source ∩ (chartAt ℂ j).source) :
    multiplierChartTransition L χ i j =ᶠ[𝓝 b] fun _ => multiplierChartTransition L χ i j b := by
  filter_upwards [multiplierChartShift_constant L hb] with w hw
  simp only [multiplierChartTransition,hw]

/-- The sign multipliers on the actual quotient atlas define a mathlib
rank-one complex vector bundle. -/
noncomputable def analyticMultiplierBundleCore (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    VectorBundleCore ℂ (PeriodTorus L) ℂ (PeriodTorus L) where
  baseSet i := (chartAt ℂ i).source
  isOpen_baseSet i := (chartAt ℂ i).open_source
  indexAt := id
  mem_baseSet_at := mem_chart_source ℂ
  coordChange := multiplierChartTransition L χ
  coordChange_self i b _ v := by
    have h : multiplierChartShift L i i b = 0 := Subtype.ext (sub_self _)
    simp [multiplierChartTransition,h,paritySign_zero]
  continuousOn_coordChange i j b hb := by
    have h : ContinuousAt (multiplierChartTransition L χ i j) b :=
      continuousAt_const.congr_of_eventuallyEq (multiplierChartTransition_eventually L χ hb)
    exact h.continuousWithinAt
  coordChange_comp i j k b _ v := by
    have h : multiplierChartShift L i k b = multiplierChartShift L j k b+multiplierChartShift L i j b := by
      apply Subtype.ext
      change _-_ = (_-_)+(_-_)
      abel
    simp [multiplierChartTransition,h,paritySign_add,mul_assoc]

/-- The standard vector bundle is complex analytic, since all changes of
fiber coordinates are locally constant signs. -/
instance analyticMultiplierBundleCore_analytic (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    (analyticMultiplierBundleCore L χ).IsContMDiff 𝓘(ℂ) ω where
  contMDiffOn_coordChange i j b hb := by
    have he := multiplierChartTransition_eventually L χ (i := i) (j := j) (b := b) hb
    exact (contMDiffAt_const.congr_of_eventuallyEq he).contMDiffWithinAt

noncomputable def multiplierBundleFiberEquiv (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (b : PeriodTorus L) :
    multiplierLineFiber L χ b ≃ₗ[ℂ] (analyticMultiplierBundleCore L χ).Fiber b :=
  multiplierFiberEval L χ b ⟨latticeSignCoverMk L χ (multiplierChartLift L b b,0),multiplierChartLift_proj L b b⟩

theorem multiplierBundleFiberEquiv_section (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (S : MultiplierLineSection L χ) (b : PeriodTorus L) :
    multiplierBundleFiberEquiv L χ b (S b) = multiplierSectionPlane L χ S (multiplierChartLift L b b) :=
  (multiplierSectionEval_at L χ S b ⟨latticeSignCoverMk L χ (multiplierChartLift L b b,0),multiplierChartLift_proj L b b⟩).symm

/-- The actual vector-bundle trivialization converts a section of the odd
fibers to its scalar lifted coefficient in each chosen plane chart. -/
theorem analyticMultiplierBundle_local_section (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (S : MultiplierLineSection L χ) (i b : PeriodTorus L) :
    ((analyticMultiplierBundleCore L χ).localTriv i
      ⟨b,multiplierBundleFiberEquiv L χ b (S b)⟩).2 = multiplierSectionPlane L χ S (multiplierChartLift L i b) := by
  change paritySign (χ (multiplierChartShift L b i b))*(show ℂ from multiplierBundleFiberEquiv L χ b (S b)) = _
  rw [multiplierBundleFiberEquiv_section,← multiplierSectionPlane_translate L χ S _ (multiplierChartShift L b i b)]
  congr 1
  change _+(_-_) = _
  abel

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analyticMultiplierBundleCore_analytic
#print axioms TwoAxisHelicoid.analyticMultiplierBundle_local_section
