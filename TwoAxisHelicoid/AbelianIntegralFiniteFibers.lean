import TwoAxisHelicoid.AbelianTorusHomotopy
import TwoAxisHelicoid.LocalHolomorphicOpenMapping
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- In local holomorphic coordinates isolated zeros make every compact
fiber finite. An open mapping cannot be locally constant. -/
theorem finite_fiber_in_holomorphic_coordinates {M : Type*} [TopologicalSpace M] {F : M → ℂ}
    (op : IsOpenMap F) (prop : IsProperMap F)
    (chart : ∀ x, ∃ (e : OpenPartialHomeomorph M ℂ) (f : ℂ → ℂ), x∈e.source ∧
      AnalyticAt ℂ f (e x) ∧ F=ᶠ[𝓝 x] f ∘ e) (c : ℂ) : (F ⁻¹' {c}).Finite := by
  apply (prop.isCompact_preimage isCompact_singleton).finite
  apply isDiscrete_iff_nhdsNE.mpr
  intro x inside
  rw [inf_principal_eq_bot]
  obtain ⟨e,f,hx,an,germ⟩ := chart x
  rcases an.eventually_eq_or_eventually_ne (analyticAt_const (v := c)) with loc|iso
  · have constant : ∀ᶠ y in 𝓝 x, F y=c := germ.trans ((e.continuousAt hx).tendsto.eventually loc)
    obtain ⟨W,sub,wo,xw⟩ := mem_nhds_iff.mp constant
    have img : F '' W={c} := Subset.antisymm (image_subset_iff.mpr fun y hy => sub hy)
      (singleton_subset_iff.mpr ⟨x,xw,inside⟩)
    exact (not_isOpen_singleton c (img ▸ op W wo)).elim
  · have nt : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(e.continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hx),self_mem_nhdsWithin] with y hy ne
      exact fun eq => ne (e.injOn hy hx eq)
    filter_upwards [nt.eventually iso,germ.filter_mono nhdsWithin_le_nhds] with y hy he
    exact fun h => hy (he.symm.trans h)

namespace HolomorphicCoefficientDisks

/-- Properness forces a nonconstant abelian integral on the plane
cover. In analytic surface charts it is open with finite fibers. -/
theorem proper_abelian_integral_open_finite {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {A : HolomorphicCoefficientDisks M} {p : ℂ → M} (cover : IsCoveringMap p) {D : ℂ → ℂ}
    (dev : A.IsAbelianIntegral p D) (prop : IsProperMap D) :
    IsOpenMap D ∧ Surjective D ∧ ∀ c : ℂ, (D ⁻¹' {c}).Finite := by
  have chart (z : ℂ) : ∃ (e : OpenPartialHomeomorph ℂ ℂ) (f : ℂ → ℂ), z∈e.source ∧
      AnalyticAt ℂ f (e z) ∧ D=ᶠ[𝓝 z] f ∘ e := by
    obtain ⟨l,hz,eq⟩ := cover.isLocalHomeomorph z
    let i := p z
    let a := chartAt ℂ i
    let e := l.trans a
    let k := D z-A.localIntegral i (a i)
    have h := A.primitives.mem_domain i
    have val : l z=i := (congrFun eq z).symm
    have inside : z∈e.source := ⟨hz,by change l z∈a.source; rw [val]; exact h.1⟩
    have atz : e z=a i := congrArg a val
    refine ⟨e,fun u => A.localIntegral i u+k,inside,atz ▸ (A.localIntegral_analyticAt i h.2).add analyticAt_const,?_⟩
    filter_upwards [dev i z h] with w hw
    change D w=A.localIntegral i (a (l w))+k
    rw [← eq]
    exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  have different : ∃ z w, D z≠D w := by
    by_contra! h
    have eq : D=(fun _ => D 0) := funext fun z => h z 0
    have compact := (isProperMap_const_iff (D 0)).mp (eq ▸ prop)
    exact noncompact_univ ℂ (@isCompact_univ ℂ _ compact)
  have op := open_of_nonconstant_in_holomorphic_coordinates D different chart
  have cl : IsClopen (range D) := ⟨prop.isClosedMap.isClosed_range,op.isOpen_range⟩
  exact ⟨op,range_eq_univ.mp (cl.eq_univ (range_nonempty D)),finite_fiber_in_holomorphic_coordinates op prop chart⟩

/-- The abelian integral of any nonzero holomorphic differential on the
marked torus is open, proper and onto and its actual fibers are finite.
The differential may vanish at individual points. -/
theorem torus_abelian_integral_open_finite {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L)
    (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm) {x : M} (nonzero : A.coefficient x (chartAt ℂ x x)≠0) :
    let p := mark.symm ∘ periodTorusProjection L
    ∃ D : ℂ → ℂ, A.IsAbelianIntegral p D ∧ IsProperMap D ∧ IsOpenMap D ∧ Surjective D ∧
      ∀ c : ℂ, (D ⁻¹' {c}).Finite := by

  let p := mark.symm ∘ periodTorusProjection L
  obtain ⟨D,_,_,dev,prop,_,_,_⟩ := abelian_integral_full_period_lattice mark A compat nonzero
  have cover : IsCoveringMap p := (periodTorusProjection_isCoveringMap L).homeomorph_comp mark.symm
  exact ⟨D,dev,prop,proper_abelian_integral_open_finite cover dev prop⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.torus_abelian_integral_open_finite
