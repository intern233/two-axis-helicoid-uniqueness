import TwoAxisHelicoid.TorusHolomorphicLifts
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The canonical extension forgets arbitrary values assigned at isolated
singularities. Its value is the actual punctured limit. -/
noncomputable def removableGermExtension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[≠] z) f

theorem removableGermExtension_eq {f g : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (he : f =ᶠ[𝓝[≠] z] g) :
    removableGermExtension f z = g z := by
  exact (hg.continuousWithinAt.tendsto.congr' he.symm).limUnder_eq

theorem removableGermExtension_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (he : f =ᶠ[𝓝[≠] z] g) :
    removableGermExtension f =ᶠ[𝓝 z] g := by
  have he' : ∀ᶠ w in 𝓝 z, w ≠ z → f w = g w := by
    simpa only [Filter.EventuallyEq,eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using he
  filter_upwards [hg.eventually_analyticAt,he'.eventually_nhds] with w hgw hw
  apply removableGermExtension_eq hgw.continuousAt
  by_cases hwz : w = z
  · simpa only [hwz] using he
  · have hv : f =ᶠ[𝓝 w] g := by
      filter_upwards [hw,eventually_ne_nhds hwz] with v hv hvz
      exact hv hvz
    exact hv.filter_mono nhdsWithin_le_nhds

theorem removableGermExtension_differentiable {f : ℂ → ℂ}
    (hloc : ∀ z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ f =ᶠ[𝓝[≠] z] g) :
    Differentiable ℂ (removableGermExtension f) := by
  intro z
  obtain ⟨g,hg,he⟩ := hloc z
  exact hg.differentiableAt.congr_of_eventuallyEq
    (removableGermExtension_eventuallyEq hg he)

/-- A periodic function with analytic removable germs at every possible pole
is constant away from the poles. No entire extension is assumed. -/
theorem elliptic_removable_germs_constant (L : PeriodPair) {f : ℂ → ℂ} {S : Set ℂ}
    (hS : S.Countable)
    (hshift : ∀ z ω, ω ∈ L.lattice → z ∉ S → z+ω ∉ S)
    (hf : ∀ z ∉ S, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ L.lattice → z ∉ S → f (z+ω) = f z)
    (hloc : ∀ z ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ f =ᶠ[𝓝[≠] z] g) :
    ∃ c : ℂ, ∀ z ∉ S, f z = c := by
  have hd : Differentiable ℂ (removableGermExtension f) := by
    apply removableGermExtension_differentiable
    intro z
    by_cases hz : z ∈ S
    · exact hloc z hz
    · exact ⟨f,hf z hz,Filter.EventuallyEq.rfl⟩
  have he (z : ℂ) (hz : z ∉ S) : removableGermExtension f z = f z :=
    removableGermExtension_eq (hf z hz).continuousAt Filter.EventuallyEq.rfl
  have hperiod (z ω : ℂ) (hω : ω ∈ L.lattice) :
      removableGermExtension f (z+ω) = removableGermExtension f z := by
    have hc : Continuous (fun w : ℂ => removableGermExtension f (w+ω)) :=
      hd.continuous.comp (continuous_id.add_const ω)
    have heq : (fun w : ℂ => removableGermExtension f (w+ω)) =
        removableGermExtension f := by
      apply Continuous.ext_on (hS.dense_compl ℝ) hc hd.continuous
      intro w hw
      dsimp only
      rw [he (w+ω) (hshift w ω hω hw),he w hw,hp w ω hω hw]
    exact congrFun heq z
  refine ⟨removableGermExtension f 0,?_⟩
  intro z hz
  rw [← he z hz]
  exact entire_lattice_periodic_constant L hd hperiod z 0

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.elliptic_removable_germs_constant
