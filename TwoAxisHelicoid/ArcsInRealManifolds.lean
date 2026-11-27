import TwoAxisHelicoid.JoiningSimpleArcs
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Metric Topology Filter Function
open scoped Topology unitInterval

/-- A genuine open line coordinate centred at any given point. -/
theorem open_line_at_point {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M] (p : M) :
    ∃ j : ℝ → M, IsOpenEmbedding j ∧ j 0=p := by
  let e := chartAt ℝ p
  have ep : p∈e.source := mem_chart_source _ _
  obtain ⟨r,rp,balls⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source ep))
  let a := OpenPartialHomeomorph.univBall (e p) r
  let h := a.trans e.symm
  have whole : h.source=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x∈a.source := by simp [a]
    exact ⟨hx,balls (show a x∈ball (e p) r from by
      simpa only [a,OpenPartialHomeomorph.univBall_target _ rp] using a.map_source hx)⟩
  exact ⟨h,h.isOpenEmbedding whole,by change e.symm (a 0)=p; rw [show a 0=e p from OpenPartialHomeomorph.univBall_apply_zero _ _,e.left_inv ep]⟩

/-- In a connected real one-manifold every two distinct points are
joined by an injective path. Local arcs may be straightened and trimmed
before concatenation, so self-intersections of paths are immaterial. -/
theorem real_manifold_simple_arc_joined {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] [ChartedSpace ℝ M] (p q : M) : SimpleArcJoined p q := by
  have near (z : M) : ∀ᶠ x in 𝓝 z, SimpleArcJoined z x := by
    obtain ⟨j,ej,eq⟩ := open_line_at_point z
    have jz : z∈range j := ⟨0,eq⟩
    filter_upwards [ej.isOpen_range.mem_nhds jz] with x hx
    obtain ⟨t,rfl⟩ := hx
    by_cases e : (0:ℝ)=t
    · exact Or.inl (eq.symm.trans (congrArg j e))
    · exact Or.inr ⟨((Path.segment 0 t).map ej.continuous).cast eq.symm rfl,
        ej.injective.comp (Path.segment_injective_of_ne e)⟩
  let A := {x | SimpleArcJoined p x}
  have op : IsOpen A := isOpen_iff_mem_nhds.mpr fun x hx => (near x).mono fun y hy => hx.trans hy
  have cl : IsClosed A := isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx =>
    (near x).mono fun y hy => fun hp => hx (hp.trans hy.symm))
  have all := IsClopen.eq_univ ⟨cl,op⟩ (show A.Nonempty from ⟨p,Or.inl rfl⟩)
  exact (show q∈A from all.symm ▸ mem_univ q)

/-- The intermediate value theorem and strict monotonicity on an
interval give invariance of domain for a locally injective real curve
with values in an arbitrary real one-manifold. -/
theorem real_manifold_locally_injective_curve_open {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {f : ℝ → M} (cf : Continuous f) (loc : IsLocallyInjective f) : IsOpen (range f) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t,rfl⟩
  let e := chartAt ℝ (f t)
  have ft : f t∈e.source := mem_chart_source _ _
  obtain ⟨U,ou,ut,inj⟩ := loc t
  have neigh : U∩f ⁻¹' e.source∈𝓝 t := inter_mem (ou.mem_nhds ut) (cf.continuousAt (e.open_source.mem_nhds ft))
  obtain ⟨r,rp,fit⟩ := Metric.mem_nhds_iff.mp neigh
  let a := t-r/2
  let b := t+r/2
  have at' : a<t := by dsimp [a]; linarith
  have tb : t<b := by dsimp [b]; linarith
  have ab := at'.trans tb
  have F (x : ℝ) (h : x∈Icc a b) : x∈U ∧ f x∈e.source := by
    apply fit
    rw [mem_ball,Real.dist_eq,abs_lt]
    dsimp [a,b] at h
    constructor <;> linarith [h.1,h.2]
  let g := e ∘ f
  have cg : ContinuousOn g (Icc a b) := e.continuousOn.comp cf.continuousOn (fun x hx => (F x hx).2)
  have ig : InjOn g (Icc a b) := fun x hx y hy eq =>
    inj (F x hx).1 (F y hy).1 (e.injOn (F x hx).2 (F y hy).2 eq)
  have left := left_mem_Icc.mpr ab.le
  have right := right_mem_Icc.mpr ab.le
  have mid : t∈Icc a b := ⟨at'.le,tb.le⟩
  have nb : g '' Icc a b∈𝓝 (g t) := by
    rcases cg.strictMonoOn_of_injOn_Icc' ab.le ig with inc|dec
    · rw [cg.image_Icc_of_monotoneOn ab.le inc.monotoneOn]
      exact Icc_mem_nhds (inc left mid at') (inc mid right tb)
    · rw [cg.image_Icc_of_antitoneOn ab.le dec.antitoneOn]
      exact Icc_mem_nhds (dec mid right tb) (dec left mid at')
  filter_upwards [e.open_source.mem_nhds ft,e.continuousAt ft nb] with y ys hy
  obtain ⟨v,hv,ev⟩ := hy
  exact ⟨v,e.injOn (F v hv).2 ys ev⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.real_manifold_simple_arc_joined
#print axioms TwoAxisHelicoid.real_manifold_locally_injective_curve_open
