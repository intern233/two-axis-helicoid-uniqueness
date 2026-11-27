import TwoAxisHelicoid.HarmonicLocalMaximum
import TwoAxisHelicoid.HolomorphicSurfaceIdentity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Order.LocalExtr

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Intrinsic harmonicity, expressed by a real part in a neighborhood. -/
def SurfaceHarmonicGerm {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (h : M → ℝ) (x : M) : Prop :=
  ∃ F : M → ℂ, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F x ∧ ∀ᶠ y in 𝓝 x, h y=(F y).re

/-- Harmonic comparison by the strong local maximum principle. -/
def SurfaceSubharmonicAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (u : M → ℝ) (x : M) : Prop :=
  ContinuousAt u x ∧ ∀ h : M → ℝ, SurfaceHarmonicGerm h x → IsLocalMax (fun y => u y-h y) x →
    ∀ᶠ y in 𝓝 x, u y-h y=u x-h x

theorem surface_harmonic_germ_in_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {e : OpenPartialHomeomorph M ℂ} (chart : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {x : M} (xs : x∈e.source) {h : M → ℝ} :
    SurfaceHarmonicGerm h x ↔ HarmonicAt (h ∘ e.symm) (e x) := by
  have back : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by simpa only [e.left_inv xs] using (e.symm.continuousAt (e.map_source xs)).tendsto
  constructor
  · rintro ⟨F,hf,eq⟩
    have hc := (show ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (e.symm (e x)) by rwa [e.left_inv xs]).comp (e x)
      (contMDiffAt_symm_of_mem_maximalAtlas chart (e.map_source xs))
    exact (harmonicAt_congr_nhds (f₂:=fun z => (F (e.symm z)).re) (back.eventually eq)).mpr hc.contDiffAt.analyticAt.harmonicAt_re
  · intro hh
    obtain ⟨r,rp,sub⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt _) _ hh
    obtain ⟨G,an,eq⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f:=h ∘ e.symm) (z:=e x) (R:=r) (fun _ hz => sub hz)
    refine ⟨G ∘ e,(an _ (mem_ball_self rp)).contDiffAt.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas chart xs),?_⟩
    filter_upwards [e.open_source.mem_nhds xs,(e.continuousAt xs).eventually (ball_mem_nhds (e x) rp)] with w ws wz
    exact ((eq wz).trans (congrArg h (e.left_inv ws))).symm

theorem SurfaceHarmonicGerm.sub {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M} {f g : M → ℝ}
    (hf : SurfaceHarmonicGerm f x) (hg : SurfaceHarmonicGerm g x) : SurfaceHarmonicGerm (fun y => f y-g y) x := by
  obtain ⟨F,af,eq⟩ := hf
  obtain ⟨G,ag,eq'⟩ := hg
  refine ⟨fun y => F y-G y,af.sub ag,?_⟩
  filter_upwards [eq,eq'] with y hy hy' using by simp only [hy,hy',Complex.sub_re]

theorem SurfaceHarmonicGerm.subharmonicAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {x : M} {f : M → ℝ} (hf : SurfaceHarmonicGerm f x) : SurfaceSubharmonicAt f x := by
  obtain ⟨F,af,eq⟩ := hf
  refine ⟨(Complex.continuous_re.continuousAt.comp af.continuousAt).congr_of_eventuallyEq eq,?_⟩
  intro h hh mx
  let e := chartAt ℂ x
  have xs : x∈e.source := mem_chart_source ℂ x
  have back : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by simpa only [e.left_inv xs] using (e.symm.continuousAt (e.map_source xs)).tendsto
  have ha := (surface_harmonic_germ_in_chart (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) xs).mp
    ((show SurfaceHarmonicGerm f x from ⟨F,af,eq⟩).sub hh)
  have hm : IsLocalMax (fun z => f (e.symm z)-h (e.symm z)) (e x) := by
    change ∀ᶠ z in 𝓝 (e x), f (e.symm z)-h (e.symm z)≤f (e.symm (e x))-h (e.symm (e x))
    rw [e.left_inv xs]
    exact back.eventually mx
  have cons := harmonic_eventually_constant_at_local_max ha hm
  filter_upwards [e.open_source.mem_nhds xs,(e.continuousAt xs).eventually cons] with y ys same
  change f (e.symm (e y))-h (e.symm (e y))=f (e.symm (e x))-h (e.symm (e x)) at same
  rwa [e.left_inv ys,e.left_inv xs] at same

theorem surface_subharmonic_max {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M} {f g : M → ℝ}
    (hf : SurfaceSubharmonicAt f x) (hg : SurfaceSubharmonicAt g x) :
    SurfaceSubharmonicAt (fun y => max (f y) (g y)) x := by
  have side {u v : M → ℝ} (sub : SurfaceSubharmonicAt u x) (order : v x≤u x) (h : M → ℝ)
      (hh : SurfaceHarmonicGerm h x) (mx : IsLocalMax (fun y => max (u y) (v y)-h y) x) :
      ∀ᶠ y in 𝓝 x, max (u y) (v y)-h y=max (u x) (v x)-h x := by
    have m : IsLocalMax (fun y => u y-h y) x := by
      filter_upwards [mx] with y hy
      change max (u y) (v y)-h y≤max (u x) (v x)-h x at hy
      rw [max_eq_left order] at hy
      exact (sub_le_sub_right (le_max_left _ _) _).trans hy
    filter_upwards [sub.2 h hh m,mx] with y hy hm
    apply le_antisymm hm
    rw [max_eq_left order,← hy]
    exact sub_le_sub_right (le_max_left _ _) _
  refine ⟨hf.1.max hg.1,?_⟩
  intro h hh mx
  rcases le_total (g x) (f x) with ge|le
  · exact side hf ge h hh mx
  · simpa only [max_comm (g _) (f _)] using side hg le h hh (by simpa only [max_comm (g _) (f _)] using mx)

/-- A compact set has no positive interior maximum with the plateau
property when all its boundary values are nonpositive. -/
theorem compact_boundary_maximum_principle {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [NoncompactSpace X] {K : Set X} (compact : IsCompact K) {u : X → ℝ}
    (cont : ContinuousOn u K) (edge : ∀ x∈K, x∉interior K → u x≤0)
    (plateau : ∀ x∈interior K, 0<u x → IsLocalMax u x → ∀ᶠ y in 𝓝 x, u y=u x) : ∀ x∈K, u x≤0 := by
  intro x hx
  by_contra! pos
  obtain ⟨a,ha,mx⟩ := compact.exists_isMaxOn ⟨x,hx⟩ cont
  let S := K∩u ⁻¹' {u a}
  have sc : IsCompact S := compact.of_isClosed_subset
    (by simpa only [S,inter_comm] using cont.preimage_isClosed_of_isClosed compact.isClosed (isClosed_singleton (x:=u a))) inter_subset_left
  have sn : a∈S := ⟨ha,rfl⟩
  have op : IsOpen S := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    have high : 0<u z := (pos.trans_le (mx hx)).trans_eq hz.2.symm
    have inside : z∈interior K := by_contra fun out => high.not_ge (edge z hz.1 out)
    have kn := mem_interior_iff_mem_nhds.mp inside
    have localMax : IsLocalMax u z := by
      filter_upwards [kn] with y hy using (mx hy).trans_eq hz.2.symm
    filter_upwards [kn,plateau z inside high localMax] with y hy same using ⟨hy,same.trans hz.2⟩)
  have allS := (isClopen_iff.mp (show IsClopen S from ⟨sc.isClosed,op⟩)).resolve_left (nonempty_of_mem sn).ne_empty
  exact sc.ne_univ allS

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_boundary_maximum_principle
