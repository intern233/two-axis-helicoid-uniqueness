import TwoAxisHelicoid.PiecewiseComplexPeriods
import TwoAxisHelicoid.TorusActualLifts
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Continuous differentiability of a punctured-torus path in local quotient
coordinates, including one-sided derivatives at both endpoints. -/
def TorusPathC1 {L : PeriodPair} {q r : PuncturedPeriodTorus L} (γ : Path q r) : Prop :=
  ∀ s ∈ Icc (0:ℝ) 1, ∃ g : ℝ → ℂ, ContDiffWithinAt ℝ 1 g (Icc 0 1) s ∧
    ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] s, periodTorusProjection L (g t) = (γ.extend t).1

/-- A continuously differentiable arc in the punctured quotient has a
regular plane lift from every chosen initial representative. -/
theorem punctured_torus_path_exists_C1_lift (L : PeriodPair) {q r : PuncturedPeriodTorus L}
    (γ : Path q r) (hc : TorusPathC1 γ) {x : ℂ} (hx : periodTorusProjection L x = q.1) :
    ∃ a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ, a.left = 0 ∧ a.right = 1 ∧
      a.curve 0 = x ∧ ∀ s ∈ Icc (0:ℝ) 1, periodTorusProjection L (a.curve s) = (γ.extend s).1 := by
  let δ := γ.map continuous_subtype_val
  let cov := periodTorusProjection_isCoveringMap L
  have hstart : δ 0 = periodTorusProjection L x := δ.source.trans hx.symm
  let f := cov.liftPath δ x hstart
  have h0 : f 0 = x := cov.liftPath_zero δ x hstart
  have he : periodTorusProjection L ∘ f = δ := cov.liftPath_lifts δ x hstart
  let p : Path x (f 1) := ⟨f,h0,rfl⟩
  let K := Icc (0:ℝ) 1
  have hproj (s : ℝ) (hs : s ∈ K) : periodTorusProjection L (p.extend s) = (γ.extend s).1 := by
    rw [p.extend_apply hs,γ.extend_apply hs]
    exact congrFun he ⟨s,hs⟩
  have hC : ContDiffOn ℝ 1 p.extend K := by
    intro s hs
    obtain ⟨g,hg,hl⟩ := hc s hs
    have hdiff : ContinuousWithinAt (fun t => p.extend t-g t) K s :=
      p.continuous_extend.continuousAt.continuousWithinAt.sub hg.continuousWithinAt
    have hev := hdiff.eventually (L.compl_lattice_sdiff_singleton_mem_nhds (p.extend s-g s))
    have heq : p.extend =ᶠ[𝓝[K] s] (fun t => g t+(p.extend s-g s)) := by
      filter_upwards [hl,hev,self_mem_nhdsWithin] with t ht hne hK
      have hm := (periodTorusProjection_eq_iff L (g t) (p.extend t)).mp (ht.trans (hproj t hK).symm)
      have he' : p.extend t-g t = p.extend s-g s := by
        by_contra h
        exact hne ⟨hm,h⟩
      linear_combination he'
    exact (hg.add contDiffWithinAt_const).congr_of_eventuallyEq_of_mem heq hs
  let a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ := {
    left := 0, right := 1, ordered := zero_le_one
    curve := p.extend, velocity := derivWithin p.extend K
    stays := fun s hs hn => (γ.extend s).2 ((hproj s hs).symm.trans ((periodTorusProjection_eq_zero L _).mpr hn))
    continuous_curve := p.continuous_extend.continuousOn
    continuous_velocity := hC.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
    derivative := fun s hs => ((hC.differentiableOn one_ne_zero s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
      ).hasDerivAt (Icc_mem_nhds hs.1 hs.2) }
  exact ⟨a,rfl,rfl,p.extend_zero,hproj⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_torus_path_exists_C1_lift
