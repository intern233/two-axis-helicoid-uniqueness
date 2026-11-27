import TwoAxisHelicoid.RemovableGerms
import TwoAxisHelicoid.CommonPrincipalPartRigidity

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- Equality of the Laurent principal parts gives an actual holomorphic germ
for the difference, including at points where both representatives have a
nonremovable pole. The functions may take arbitrary values at the point. -/
theorem removable_from_common_laurent_principal_part {p q : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (a : ℕ → ℂ) {s t : ℂ → ℂ} (hs : AnalyticAt ℂ s z) (ht : AnalyticAt ℂ t z)
    (hp : p =ᶠ[𝓝[≠] z] fun w => finitePrincipalPart n a z w+s w)
    (hq : q =ᶠ[𝓝[≠] z] fun w => finitePrincipalPart n a z w+t w) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ (fun w => q w-p w) =ᶠ[𝓝[≠] z] g := by
  refine ⟨t-s,ht.sub hs,?_⟩
  filter_upwards [hp,hq] with w hwp hwq
  change q w-p w = t w-s w
  rw [hwp,hwq]
  ring

/-- Periodicity and removable germs at every point determine the *same*
constant germ at every location, irrespective of the arbitrary values at
singularities. -/
theorem elliptic_removable_germs_constant_germ (L : PeriodPair) {f : ℂ → ℂ}
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    (hf : ∀ z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ f =ᶠ[𝓝[≠] z] g) :
    ∃ d : ℂ, ∀ z, f =ᶠ[𝓝[≠] z] fun _ => d := by
  let F := removableGermExtension f
  have hd := removableGermExtension_differentiable hf
  have he (z : ℂ) : f =ᶠ[𝓝[≠] z] F := by
    obtain ⟨g,hg,he⟩ := hf z
    exact he.trans ((removableGermExtension_eventuallyEq hg he).filter_mono nhdsWithin_le_nhds).symm
  have hperiod (z ω : ℂ) (hω : ω ∈ L.lattice) : F (z+ω) = F z := by
    have hT : Tendsto (fun w : ℂ => w+ω) (𝓝[≠] z) (𝓝[≠] (z+ω)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨(continuous_id.add_const ω).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        (show ∀ᶠ w in 𝓝[≠] z, w ≠ z from self_mem_nhdsWithin).mono fun _ hw h => hw (add_right_cancel h)⟩
    have e : (fun w : ℂ => F (w+ω)) =ᶠ[𝓝[≠] z] F := by
      filter_upwards [hT.eventually (he (z+ω)),he z] with w hw hfw
      exact hw.symm.trans ((hp w ω hω).trans hfw)
    have h₁ := (hd.continuous.comp (continuous_id.add_const ω)).continuousAt (x := z)
    exact tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
      ((hd z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' e.symm)
  refine ⟨F 0,fun z => (he z).trans (Eventually.of_forall fun w => ?_)⟩
  exact entire_lattice_periodic_constant L hd hperiod w 0

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.elliptic_removable_germs_constant_germ
