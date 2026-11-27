import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology OnePoint

/-- A continuous plane traversal whose projection tends to a torus
point approaches one definite lattice representative. On a sufficiently
late connected time interval its difference from a local section is
a constant lattice vector. -/
theorem plane_end_limit_of_projected_limit (L : PeriodPair) (γ : ℝ → ℂ) (cont : Continuous γ)
    {p : PeriodTorus L} (top : Tendsto (periodTorusProjection L ∘ γ) atTop (𝓝 p)) :
    ∃ z, periodTorusProjection L z=p ∧ Tendsto γ atTop (𝓝 z) := by
  let π := periodTorusProjection L
  have cπ : Continuous π := QuotientAddGroup.continuous_mk
  obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Surjective π) p
  obtain ⟨e,src,repr⟩ := periodTorusProjection_isLocalHomeomorph L z
  have atP : p=e z := hz.symm.trans (congrFun repr z)
  have pt : p∈e.target := atP.symm ▸ e.map_source src
  have ez : e.symm p=z := by rw [atP,e.left_inv src]
  let B := fun t => e.symm (π (γ t))
  have lim : Tendsto B atTop (𝓝 z) := ez ▸ (e.continuousAt_symm pt).tendsto.comp top
  obtain ⟨T,after⟩ := eventually_atTop.mp (top.eventually (e.open_target.mem_nhds pt))
  let D := fun t => γ t-B t
  have cb : ContinuousOn B (Ici T) := e.continuousOn_symm.comp (cπ.comp cont).continuousOn (fun t ht => after t ht)
  have latt : MapsTo D (Ici T) (L.lattice : Set ℂ) := by
    intro t ht
    apply (periodTorusProjection_eq_iff L (B t) (γ t)).mp
    exact (congrFun repr _).trans (e.right_inv (after t ht))
  have discrete : IsDiscrete (L.lattice : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  have loc (t : ℝ) (ht : T≤t) : D t=D T :=
    isPreconnected_Ici.constant_of_mapsTo discrete (cont.continuousOn.sub cb) latt ht (show T∈Ici T from le_refl T)
  refine ⟨z+D T,(periodTorusProjection_add_lattice L _ _ (latt (show T∈Ici T from le_refl T))).trans hz,?_⟩
  apply (lim.add (tendsto_const_nhds (x:=D T))).congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  have eq := loc t ht
  change γ t-B t=D T at eq
  rw [← eq]
  abel

/-- Distinct endpoints in the covering plane are forced by a marked
angle obstruction on the compactified trajectory itself. -/
theorem obstructed_torus_orbit_has_distinct_plane_ends (L : PeriodPair) (γ : ℝ → ℂ) (cont : Continuous γ)
    (g : C(OnePoint ℝ,PeriodTorus L)) (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (real : ∀ t : ℝ, g t=periodTorusProjection L (γ t))
    (fail : ¬∃ u v : C(OnePoint ℝ,ℝ), ∀ q, normalizedPhase (u q)=(H (g q)).1 ∧
      normalizedPhase (v q)=(H (g q)).2) :
    ∃ a b : ℂ, periodTorusProjection L a=g ∞ ∧ periodTorusProjection L b=g ∞ ∧ a≠b ∧
      Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b) := by
  let π := periodTorusProjection L
  have both : Tendsto (π ∘ γ) (cocompact ℝ) (𝓝 (g ∞)) := by
    rw [← coclosedCompact_eq_cocompact]
    exact (g.continuous.continuousAt.tendsto.comp OnePoint.tendsto_coe_infty).congr real
  rw [cocompact_eq_atBot_atTop,tendsto_sup] at both
  obtain ⟨b,bp,blim⟩ := plane_end_limit_of_projected_limit L γ cont both.2
  obtain ⟨a,ap,rev⟩ := plane_end_limit_of_projected_limit L (fun t => γ (-t)) (cont.comp continuous_neg)
    (both.1.comp tendsto_neg_atTop_atBot)
  have alim : Tendsto γ atBot (𝓝 a) := by simpa only [comp_def,neg_neg] using rev.comp tendsto_neg_atBot_atTop
  refine ⟨a,b,ap,bp,?_,alim,blim⟩
  rintro rfl
  have common : Tendsto γ (coclosedCompact ℝ) (𝓝 a) := by
    rw [coclosedCompact_eq_cocompact,cocompact_eq_atBot_atTop]
    exact alim.sup blim
  let Γ := OnePoint.continuousMapMk ⟨γ,cont⟩ a common
  let u := fun (i : Fin 2) => (⟨fun q => L.basis.repr (Γ q) i,
    (L.basis.coord i).continuous_of_finiteDimensional.comp Γ.continuous⟩ : C(OnePoint ℝ,ℝ))
  have rep (q : OnePoint ℝ) : π (Γ q)=g q := by
    induction q using OnePoint.rec with
    | infty => exact ap
    | coe t => exact (real t).symm
  apply fail
  refine ⟨u 0,u 1,fun q => ?_⟩
  rw [← rep,marked]
  exact ⟨rfl,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_end_limit_of_projected_limit
#print axioms TwoAxisHelicoid.obstructed_torus_orbit_has_distinct_plane_ends
