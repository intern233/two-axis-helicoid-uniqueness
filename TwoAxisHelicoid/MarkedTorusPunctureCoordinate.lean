import TwoAxisHelicoid.ProjectedHeightChart
import TwoAxisHelicoid.PuncturedEndInverseEscape
import TwoAxisHelicoid.PuncturedCurveNoncompact
import TwoAxisHelicoid.PointedTorusUniformization
import TwoAxisHelicoid.PeriodicHeightRigidity

namespace TwoAxisHelicoid
open Complex Metric Set Filter
open scoped Topology

/-- The natural affine lattice parameter itself, centered at the deleted
point, is a compactifying chart of the punctured marked torus. Its
inverse really is the quotient projection on the whole punctured disk. -/
theorem marked_torus_puncture_coordinate (L : PeriodPair) :
    ∃ E : PuncturedComplexEnd (PuncturedPeriodTorus L),
      ∀ z∈E.coord.target, (E.coord.symm z).1=periodTorusProjection L z := by
  classical
  let := periodTorus_compactSpace L
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  obtain ⟨b,hb⟩ := (marked_torus_lattice_complement_connected L).nonempty
  let b0 : PuncturedPeriodTorus L := ⟨periodTorusProjection L b,fun eq => hb ((periodTorusProjection_eq_zero L b).mp eq)⟩
  obtain ⟨P,src,proj⟩ := periodTorusProjection_isLocalHomeomorph L (0:ℂ)
  have zero : P 0=0 := by rw [← proj]; exact (periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem
  have op : IsOpenMap (P : ℂ → PeriodTorus L) := by rw [← proj]; exact QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  let U := puncturedPeriodTorusOpen L
  let d := P.symm.subtypeRestr (s := U) ⟨b0⟩
  have inChart (z : ℂ) (hz : z∈P.source) (q : PuncturedPeriodTorus L) (eq : P z=q.1) :
      q∈d.source ∧ d q=z := by
    have y : q.1∈P.target := eq ▸ P.map_source hz
    refine ⟨?_,?_⟩
    · change q∈(P.symm.subtypeRestr (s := U) ⟨b0⟩).source
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact y
    · change P.symm q.1=z
      rw [← eq,P.left_inv hz]
  have punct : ∀ᶠ z in 𝓝[≠] (0:ℂ), z∈d.target ∧ (d.symm z).1=periodTorusProjection L z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (P.open_source.mem_nhds src),self_mem_nhdsWithin] with z hz nz
    have ne : P z≠0 := fun eq => nz (P.injOn hz src (eq.trans zero.symm))
    let q : PuncturedPeriodTorus L := ⟨P z,ne⟩
    obtain ⟨inside,back⟩  := inChart z hz q rfl
    have f := d.left_inv inside
    rw [back] at f
    exact ⟨back ▸ d.map_source inside,(congrArg Subtype.val f).trans (congrFun proj z).symm⟩
  obtain ⟨r,hr,near⟩ := Metric.mem_nhdsWithin_iff.mp punct
  let V := ball (0:ℂ) r \ {0}
  let e := d.trans (OpenPartialHomeomorph.ofSet V (isOpen_ball.sdiff isClosed_singleton))
  have gt (z : ℂ) (hz : z∈V) := near (show z∈ball (0:ℂ) r ∩ {0}ᶜ from hz)
  have et : e.target=V := by ext z; change z∈V ∧ z∈d.target ↔ _; exact ⟨And.left,fun h => ⟨h,(gt z h).1⟩⟩
  have transfer {A : PuncturedPeriodTorus L → Prop}
      (h : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ q : PuncturedPeriodTorus L, P z=q.1 → A q) :
      ∀ᶠ q in cocompact (PuncturedPeriodTorus L), A q := by
    obtain ⟨K,compact,holds⟩ := compact_puncture_projected_property op zero h
    filter_upwards [compact.compl_mem_cocompact] with q hq using holds q hq
  have core : IsCompact e.sourceᶜ := by
    have mem : e.source∈cocompact (PuncturedPeriodTorus L) := by
      apply transfer
      filter_upwards [mem_nhdsWithin_of_mem_nhds (P.open_source.mem_nhds src),
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin] with z hz small nz
      intro q eq
      obtain ⟨s,bk⟩  := inChart z hz q eq
      refine ⟨s,?_⟩
      change d q∈V
      rw [bk]
      exact ⟨small,nz⟩
    obtain ⟨K,cK,sub⟩ := mem_cocompact.mp mem
    exact cK.of_isClosed_subset e.open_source.isClosed_compl (fun q hq => by by_contra h; exact hq (sub h))
  have tend : Tendsto e (cocompact (PuncturedPeriodTorus L)) (𝓝 0) := by
    apply tendsto_def.mpr
    intro W hW
    apply transfer
    filter_upwards [mem_nhdsWithin_of_mem_nhds (P.open_source.mem_nhds src),mem_nhdsWithin_of_mem_nhds hW] with z hz hzW
    intro q eq
    change d q∈W
    rwa [(inChart z hz q eq).2]
  exact ⟨puncturedComplexEndOfChart e hr et core tend,fun z hz => (gt z (et ▸ hz)).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_puncture_coordinate
