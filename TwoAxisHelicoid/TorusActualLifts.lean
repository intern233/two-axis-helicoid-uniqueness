import TwoAxisHelicoid.TorusLocalHolomorphic
import TwoAxisHelicoid.TorusHolomorphicLifts
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set

theorem periodTorusProjection_isCoveringMap (L : PeriodPair) :
    IsCoveringMap (periodTorusProjection L) := by
  have hd : IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  exact (L.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm hd).isCoveringMap

/-- A lift is constructed through the actual covering map; it is not included
as an extra hypothesis on a torus map. -/
theorem torus_continuous_map_has_lift (L M : PeriodPair)
    {f : PeriodTorus L → PeriodTorus M} (hf : Continuous f)
    (z₀ w₀ : ℂ) (hzero : periodTorusProjection M w₀ = f (periodTorusProjection L z₀)) :
    ∃ F : ℂ → ℂ, Continuous F ∧ F z₀ = w₀ ∧
      ∀ z, periodTorusProjection M (F z) = f (periodTorusProjection L z) := by
  let g : C(ℂ,PeriodTorus M) := ⟨fun z => f (periodTorusProjection L z),
    hf.comp QuotientAddGroup.continuous_mk⟩
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := (periodTorusProjection_isCoveringMap M).existsUnique_continuousMap_lifts
    g z₀ w₀ hzero
  exact ⟨F,F.continuous,hF0,fun z => congrFun hFl z⟩

theorem torus_continuous_lift_lattice_increments (L M : PeriodPair)
    {f : PeriodTorus L → PeriodTorus M} {F : ℂ → ℂ} (hF : Continuous F)
    (hlift : ∀ z, periodTorusProjection M (F z) = f (periodTorusProjection L z))
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ v ∈ M.lattice, ∀ z, F (z+ω) = F z+v := by
  have hm (z : ℂ) : F (z+ω)-F z ∈ M.lattice := by
    apply (periodTorusProjection_eq_iff M (F z) (F (z+ω))).mp
    rw [hlift,hlift,periodTorusProjection_add_lattice L z ω hω]
  refine ⟨F ω-F 0,by simpa using hm 0,?_⟩
  intro z
  have he := continuous_lattice_valued_constant M
    ((hF.comp (continuous_id.add continuous_const)).sub hF) hm z 0
  change F (z+ω)-F z = F (0+ω)-F 0 at he
  simp only [zero_add] at he
  linear_combination he

theorem torus_holomorphic_map_has_entire_lift (L M : PeriodPair)
    {f : PeriodTorus L → PeriodTorus M} (hf : TorusHolomorphic L M f)
    (z₀ w₀ : ℂ) (hzero : periodTorusProjection M w₀ = f (periodTorusProjection L z₀)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F z₀ = w₀ ∧
      (∀ z, periodTorusProjection M (F z) = f (periodTorusProjection L z)) ∧
      ∀ ω ∈ L.lattice, ∃ v ∈ M.lattice, ∀ z, F (z+ω) = F z+v := by
  obtain ⟨F,hF,hF0,hl⟩ := torus_continuous_map_has_lift L M hf.continuous z₀ w₀ hzero
  exact ⟨F,torus_holomorphic_continuous_lift_analytic hf hF hl,hF0,hl,
    torus_continuous_lift_lattice_increments L M hF hl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_holomorphic_map_has_entire_lift
