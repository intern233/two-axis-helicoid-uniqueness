import TwoAxisHelicoid.RhombicGlobalPrimitive
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

/-- Every regular point can be translated either into the open horizontal
strip or into the pole-free bridge rectangle. -/
theorem rhombic_primitive_patch_cover {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    ∃ ω ∈ (rhombicPeriodPair t ht).lattice,
      z-ω ∈ complexHorizontalStrip 0 t ∨ z-ω ∈ complexOpenRect (-2) 0 (-t) t := by
  have hb := rhombicRowPoint_im_bounds ht z
  by_cases hpos : 0 < (rhombicRowPoint t z).im
  · let ω := rhombicIntegerPeriod t 0 (rhombicRowIndex t z)
    refine ⟨ω,rhombicIntegerPeriod_mem ht _ _,Or.inl ?_⟩
    have he : z-ω = rhombicRowPoint t z := by
      dsimp [ω,rhombicIntegerPeriod,rhombicRowPoint]
      simp
    rw [he]
    exact ⟨hpos,hb.2⟩
  · have hzero : (rhombicRowPoint t z).im = 0 := le_antisymm (le_of_not_gt hpos) hb.1
    let ω := rhombicIntegerPeriod t (rhombicGapIndex t z) (rhombicRowIndex t z)
    refine ⟨ω,rhombicIntegerPeriod_mem ht _ _,Or.inr ?_⟩
    have he : z-ω = rhombicGapPoint t z := by
      dsimp [ω,rhombicIntegerPeriod,rhombicGapPoint,rhombicRowPoint]
      ring
    rw [he]
    refine ⟨rhombicGapPoint_re_strict_of_row ht hz hzero,?_⟩
    rw [rhombicGapPoint_im,hzero]
    exact ⟨by linarith,ht⟩

/-- Actual local holomorphic primitives witness the regularity of the
constructed global real primitive, including points on a lattice row.
There is no all-loops period assumption: only the two displayed generator
integrals occur among the hypotheses. -/
theorem rhombicGlobalRealPrimitive_local_holomorphic {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ HasDerivAt G (f z) z ∧
      rhombicGlobalRealPrimitive t f =ᶠ[𝓝 z] fun w => (G w).re := by
  obtain ⟨ω,hω,hcover⟩ := rhombic_primitive_patch_cover ht hz
  have hpatch : ∃ U : Set ℂ, IsOpen U ∧ z-ω ∈ U ∧
      (∀ w ∈ U, HasDerivAt (rhombicWedgePrimitive t f) (f w) w) ∧
      (∀ w ∈ U, rhombicGlobalRealPrimitive t f w = (rhombicWedgePrimitive t f w).re) := by
    rcases hcover with hs | hb
    · exact ⟨complexHorizontalStrip 0 t,complexHorizontalStrip_isOpen 0 t,hs,
        fun w hw => rhombicWedgePrimitive_hasDerivAt_strip ht hf hw,
        fun w hw => rhombicGlobalRealPrimitive_on_strip ht f hw⟩
    · exact ⟨complexOpenRect (-2) 0 (-t) t,complexOpenRect_isOpen (-2) 0 (-t) t,hb,
        fun w hw => rhombicWedgePrimitive_hasDerivAt_bridge ht hf hw,
        fun w hw => rhombicGlobalRealPrimitive_on_bridge ht hf hp hu hw⟩
  obtain ⟨U,hU,hzU,hF,hmatch⟩ := hpatch
  let G : ℂ → ℂ := fun w => rhombicWedgePrimitive t f (w-ω)
  have hFA : AnalyticAt ℂ (rhombicWedgePrimitive t f) (z-ω) :=
    DifferentiableOn.analyticAt (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (hU.mem_nhds hzU)
  have hG : AnalyticAt ℂ G z := hFA.comp (f := fun w : ℂ => w-ω) (by fun_prop)
  have hfv : f (z-ω) = f z := by
    have h := hp (z-ω) ω hω
    simpa only [sub_add_cancel] using h.symm
  have hGD : HasDerivAt G (f z) z := by
    have h := (hF (z-ω) hzU).comp z ((hasDerivAt_id z).sub_const ω)
    simpa only [Function.comp_def,id_eq,mul_one,hfv] using h
  refine ⟨G,hG,hGD,?_⟩
  have hcont : Tendsto (fun w : ℂ => w-ω) (𝓝 z) (𝓝 (z-ω)) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto
  filter_upwards [hcont.eventually (hU.mem_nhds hzU)] with w hw
  have he := rhombicGlobalRealPrimitive_add_lattice ht hf hp hd hu (w-ω) ω hω
  rw [sub_add_cancel] at he
  exact he.trans (hmatch (w-ω) hw)

noncomputable def realCoefficientDerivative (v : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) v).restrictScalars ℝ)

@[simp] theorem realCoefficientDerivative_apply (v w : ℂ) :
    realCoefficientDerivative v w = (w*v).re := rfl

theorem rhombicGlobalRealPrimitive_hasFDerivAt {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasFDerivAt (rhombicGlobalRealPrimitive t f) (realCoefficientDerivative (f z)) z := by
  obtain ⟨G,_,hG,he⟩ := rhombicGlobalRealPrimitive_local_holomorphic ht hf hp hd hu hz
  exact (Complex.reCLM.hasFDerivAt.comp z (hG.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq he

theorem rhombicGlobalRealPrimitive_analyticAt {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    AnalyticAt ℝ (rhombicGlobalRealPrimitive t f) z := by
  obtain ⟨G,hG,_,he⟩ := rhombicGlobalRealPrimitive_local_holomorphic ht hf hp hd hu hz
  exact ((Complex.reCLM.analyticAt (G z)).comp (hG.restrictScalars (𝕜 := ℝ))).congr he.symm

theorem rhombicGlobalRealPrimitive_harmonicAt {t : ℝ} (ht : 0 < t) {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω) = f z)
    (hd : (rhombicDownPeriod t f).re = 0) (hu : (rhombicUpPeriod t f).re = 0)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    InnerProductSpace.HarmonicAt (rhombicGlobalRealPrimitive t f) z := by
  obtain ⟨G,hG,_,he⟩ := rhombicGlobalRealPrimitive_local_holomorphic ht hf hp hd hu hz
  exact (InnerProductSpace.harmonicAt_congr_nhds he).mpr hG.harmonicAt_re

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicGlobalRealPrimitive_hasFDerivAt
#print axioms TwoAxisHelicoid.rhombicGlobalRealPrimitive_harmonicAt
