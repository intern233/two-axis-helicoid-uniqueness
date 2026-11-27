import TwoAxisHelicoid.PeriodTorusConjugation
import Mathlib.Topology.Connected.TotallyDisconnected

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Holomorphicity in the natural quotient coordinates: a map has a local
analytic lift near each point of the universal covering plane. -/
def TorusHolomorphic (L M : PeriodPair) (f : PeriodTorus L → PeriodTorus M) : Prop :=
  ∀ z : ℂ, ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧
    ∀ᶠ w in 𝓝 z, periodTorusProjection M (F w) = f (periodTorusProjection L w)

theorem TorusHolomorphic.continuous {L M : PeriodPair}
    {f : PeriodTorus L → PeriodTorus M} (hf : TorusHolomorphic L M f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  obtain ⟨F,hF,he⟩ := hf z
  apply QuotientAddGroup.isOpenQuotientMap_mk.continuousAt_comp_iff.mp
  exact ((QuotientAddGroup.continuous_mk.continuousAt).comp hF.continuousAt).congr he

theorem continuousAt_eventually_lattice_constant (L : PeriodPair) {F : ℂ → ℂ} {z : ℂ}
    (hF : ContinuousAt F z) (hm : ∀ᶠ w in 𝓝 z, F w ∈ L.lattice) :
    ∀ᶠ w in 𝓝 z, F w = F z := by
  have hn := hF.eventually (L.compl_lattice_sdiff_singleton_mem_nhds (F z))
  filter_upwards [hm,hn] with w hw hn
  by_contra hne
  exact hn ⟨hw,hne⟩

theorem continuous_lattice_valued_constant (L : PeriodPair) {F : ℂ → ℂ}
    (hF : Continuous F) (hm : ∀ z, F z ∈ L.lattice) (z w : ℂ) : F z = F w := by
  let g : ℂ → L.lattice := fun z => ⟨F z,hm z⟩
  have hg : Continuous g := hF.subtype_mk hm
  have he : g z = g w := (isPreconnected_range hg).subsingleton ⟨z,rfl⟩ ⟨w,rfl⟩
  exact congrArg Subtype.val he

/-- Analyticity of an arbitrary continuous global lift follows from ordinary
local quotient-coordinate analyticity. -/
theorem torus_holomorphic_continuous_lift_analytic {L M : PeriodPair}
    {f : PeriodTorus L → PeriodTorus M} (hf : TorusHolomorphic L M f)
    {F : ℂ → ℂ} (hF : Continuous F)
    (hlift : ∀ z, periodTorusProjection M (F z) = f (periodTorusProjection L z)) :
    Differentiable ℂ F := by
  intro z
  obtain ⟨G,hG,he⟩ := hf z
  have hm : ∀ᶠ w in 𝓝 z, F w-G w ∈ M.lattice := by
    filter_upwards [he] with w hw
    apply (periodTorusProjection_eq_iff M (G w) (F w)).mp
    exact hw.trans (hlift w).symm
  have hd := continuousAt_eventually_lattice_constant M (hF.continuousAt.sub hG.continuousAt) hm
  have heq : (fun w => G w+(F z-G z)) =ᶠ[𝓝 z] F := by
    filter_upwards [hd] with w hw
    change F w-G w = F z-G z at hw
    linear_combination -hw
  exact ((hG.add analyticAt_const).congr heq).differentiableAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_holomorphic_continuous_lift_analytic
