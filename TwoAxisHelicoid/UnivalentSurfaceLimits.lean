import TwoAxisHelicoid.LocallyBoundedChartLimits
import TwoAxisHelicoid.UnivalentHolomorphicLimits
import TwoAxisHelicoid.UnivalentSurfaceCoordinate
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology ContDiff Manifold

/-- Hurwitz applies even to two points in different charts of an
abstract surface. Subtract the value at the first point and use a
small chart around the second point disjoint from the first. -/
theorem exhausting_univalent_surface_limit_injective {M ι : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M]
    {l : Filter ι} [l.NeBot] {U : ι → Set M} {F : ι → M → ℂ}
    (op : ∀ i, IsOpen (U i)) (hol : ∀ i, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F i) (U i))
    (inj : ∀ i, InjOn (F i) (U i)) (exhaust : ∀ K : Set M, IsCompact K → ∀ᶠ i in l, K⊆U i)
    {f : M → ℂ} (an : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (point : ∀ x, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (charts : ∀ x : M, ∃ r : ℝ, 0<r ∧ closedBall (chartAt ℂ x x) r⊆(chartAt ℂ x).target ∧
      TendstoLocallyUniformlyOn (fun i => F i ∘ (chartAt ℂ x).symm) (f ∘ (chartAt ℂ x).symm)
        l (ball (chartAt ℂ x x) r))
    (non : ∀ b, ¬ (∀ x, f x=b)) : Injective f := by
  intro x y eq
  by_contra ne
  let e := chartAt ℂ y
  have ys : y∈e.source := mem_chart_source ℂ y
  have yt := e.map_source ys
  obtain ⟨r,rp,sub,conv⟩ := charts y
  have sep : ∀ᶠ z in 𝓝 (e y), e.symm z≠x := (e.symm.continuousAt yt).eventually
    (isOpen_ne.mem_nhds (show e.symm (e y)≠x by rw [e.left_inv ys]; exact Ne.symm ne))
  have near : ∀ᶠ z in 𝓝 (e y), z∈ball (e y) r ∧ e.symm z≠x := by
    filter_upwards [sep,ball_mem_nhds (e y) rp] with z h hz using ⟨hz,h⟩
  obtain ⟨d,dp,small⟩ := Metric.nhds_basis_closedBall.mem_iff.mp near
  let V := ball (e y) d
  have inside : V⊆ball (e y) r := fun z hz => (small (ball_subset_closedBall hz)).1
  have within : closedBall (e y) d⊆e.target := fun z hz => sub (ball_subset_closedBall (small hz).1)
  let K := insert x (e.symm '' closedBall (e y) d)
  have compact : IsCompact K := ((isCompact_closedBall _ _).image_of_continuousOn
    (e.symm.continuousOn.mono within)).insert x
  have uniform := (conv.mono inside).sub ((point x).tendstoUniformlyOn_const V).tendstoLocallyUniformlyOn
  let G := fun i z => F i (e.symm z)-F i x
  let g := fun z => f (e.symm z)-f x
  have inner : e y∈V := mem_ball_self dp
  have zero : g (e y)=0 := by simp [g,e.left_inv ys,eq]
  have germ := zero_free_holomorphic_limit_local (F:=G) (f:=g) isOpen_ball uniform
    ((exhaust K compact).mono fun i covers => by
      have mem (w : ℂ) (hw : w∈V) : e.symm w∈U i :=
        covers (mem_insert_of_mem _ (mem_image_of_mem _ (ball_subset_closedBall hw)))
      refine ⟨?_,?_⟩
      · intro w hw
        have h := ((hol i).contMDiffAt ((op i).mem_nhds (mem w hw))).comp w
          (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) y)
            (within (ball_subset_closedBall hw)))
        exact h.contDiffAt.analyticAt.differentiableAt.sub_const _ |>.differentiableWithinAt
      · intro w hw eq'
        exact (small (ball_subset_closedBall hw)).2 (inj i (mem w hw) (covers (mem_insert _ _)) (sub_eq_zero.mp eq'))) inner zero
  apply non (f x)
  apply holomorphic_surface_constant_of_germ an (p:=y)
  filter_upwards [e.open_source.mem_nhds ys,(e.continuousAt ys).eventually germ] with w hw eq'
  change f (e.symm (e w))-f x=0 at eq'
  rwa [e.left_inv hw,sub_eq_zero] at eq'

/-- Normalized bounded-on-compacts univalent charts on exhausting
open neighborhoods yield a global univalent holomorphic coordinate.
Normalization of the first derivative prevents a constant limit. -/
theorem surface_coordinate_of_bounded_exhaustion {M ι : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M]
    (l : Ultrafilter ι) (U : ι → Set M) (F : ι → M → ℂ)
    (op : ∀ i, IsOpen (U i)) (hol : ∀ i, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F i) (U i)) (inj : ∀ i, InjOn (F i) (U i))
    (bounded : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0<C ∧ ∀ᶠ i in (l : Filter ι), K⊆U i ∧ ∀ z∈K, ‖F i z‖≤C)
    (p : M) (normalized : ∀ᶠ i in (l : Filter ι), deriv (F i ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=1) :
    ∃ f : M → ℂ, Injective f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  obtain ⟨f,an,point,charts⟩ := exhausting_surface_holomorphic_normal_limit l U F op hol bounded
  have ex (K : Set M) (ck : IsCompact K) := (bounded K ck).choose_spec.2.mono fun _ h => h.1
  refine ⟨f,exhausting_univalent_surface_limit_injective op hol inj ex an point charts ?_,an⟩
  let e := chartAt ℂ p
  obtain ⟨r,rp,sub,conv⟩ := charts p
  let K := e.symm '' closedBall (e p) r
  have ck : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono sub)
  have dc := conv.deriv ((ex K ck).mono fun i hi w hw => by
    have hm := hi (mem_image_of_mem _ (ball_subset_closedBall hw))
    have h := ((hol i).contMDiffAt ((op i).mem_nhds hm)).comp w
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) p) (sub (ball_subset_closedBall hw)))
    exact h.contDiffAt.analyticAt.differentiableAt.differentiableWithinAt) isOpen_ball
  have val : deriv (f ∘ e.symm) (e p)=1 := tendsto_nhds_unique (dc.tendsto_at (mem_ball_self rp))
    (tendsto_const_nhds.congr' (normalized.mono fun _ h => h.symm))
  intro b equal
  have germ : f ∘ e.symm =ᶠ[𝓝 (e p)] fun _ => b := .of_forall fun z => equal (e.symm z)
  exact one_ne_zero (val.symm.trans (germ.deriv_eq.trans (deriv_const _ _)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_coordinate_of_bounded_exhaustion
