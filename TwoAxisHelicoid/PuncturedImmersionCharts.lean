import TwoAxisHelicoid.ImmersionAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

variable {M E A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Inverse charts of a manifold without boundary have injective actual
manifold derivatives throughout their targets. -/
theorem chart_symm_mfderiv_injective (x : M) {y : E}
    (hy : y ∈ (chartAt E x).target) :
    Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x).symm y) := by
  have hh := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := 𝓘(ℝ,E)) (x := x) (y := y) (by simpa only [mfld_simps] using hy)
  have hcomp : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x) ((chartAt E x).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x).symm y) = ContinuousLinearMap.id ℝ E := by
    simpa only [mfld_simps, mfderivWithin_univ] using! hh
  have hleft : Function.LeftInverse
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x) ((chartAt E x).symm y))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x).symm y) := by
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using!
      congrArg (fun f : E →L[ℝ] E => f v) hcomp
  exact hleft.injective

/-- Smoothness and injective manifold derivative on the original
punctured manifold supply the finite-point regular charts required for
capping. No regularity of the capped map is assumed. -/
theorem punctured_immersion_regular_charts [T1Space M] {F : M → A} {p : M}
    (hF : ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x)
    (hi : ∀ x ≠ p, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x)) :
    ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M E,
      RegularImmersionChart F e ∧ p ∉ e.source ∧ x ∈ e.source := by
  intro x hx
  let e := (chartAt E x).restrOpen ({p}ᶜ) isOpen_compl_singleton
  refine ⟨e,?_,?_,?_⟩
  · intro y hy
    have hy₁ : y ∈ (chartAt E x).target := hy.1
    have hy₂ : (chartAt E x).symm y ≠ p := hy.2
    have hsy := (chartAt E x).map_target hy₁
    have hs := (contMDiffAt_iff_source_of_mem_source hsy).mp (hF _ hy₂)
    have hs' : ContDiffAt ℝ ∞ (F ∘ (chartAt E x).symm) y := by
      simpa only [mfld_simps, (chartAt E x).right_inv hy₁,
        contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt] using hs
    refine ⟨hs',?_⟩
    change Function.Injective (fderiv ℝ (F ∘ (chartAt E x).symm) y)
    have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x).symm y := by
      simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
        (mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ,E)) (x := x)
          (z := y) (by simpa only [mfld_simps] using hy₁))
    have hd := mfderiv_comp y ((hF _ hy₂).mdifferentiableAt (by simp)) hc
    have hj := (hi _ hy₂).comp (chart_symm_mfderiv_injective x hy₁)
    change Function.Injective ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F ((chartAt E x).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x).symm y)) at hj
    rw [← hd] at hj
    simpa only [mfderiv_eq_fderiv, mfld_simps] using! hj
  · intro hp
    exact hp.2 rfl
  · exact ⟨mem_chart_source E x,hx⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.chart_symm_mfderiv_injective
#print axioms TwoAxisHelicoid.punctured_immersion_regular_charts
