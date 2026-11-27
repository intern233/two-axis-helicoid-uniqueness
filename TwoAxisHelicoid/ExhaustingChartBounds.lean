import TwoAxisHelicoid.UnivalentDiskGrowth
import TwoAxisHelicoid.UnivalentSurfaceLimits

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology
open scoped Topology ContDiff Manifold BigOperators

/-- There is a fixed coordinate disk about each point on which every
sufficiently late exhaustion map is holomorphic and univalent. -/
theorem eventual_univalent_chart_disk {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {l : Filter ι} {U : ι → Set M} {F : ι → M → ℂ}
    (op : ∀ i, IsOpen (U i)) (hol : ∀ i, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F i) (U i))
    (inj : ∀ i, InjOn (F i) (U i)) (exhaust : ∀ K : Set M, IsCompact K → ∀ᶠ i in l, K⊆U i) (x : M) :
    ∃ r : ℝ, 0<r ∧ closedBall (chartAt ℂ x x) (4*r)⊆(chartAt ℂ x).target ∧
      ∀ᶠ i in l, AnalyticOnNhd ℂ (F i ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) (4*r)) ∧
        InjOn (F i ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) (4*r)) := by
  let e := chartAt ℂ x
  have xs : x∈e.source := mem_chart_source ℂ x
  obtain ⟨d,dp,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source xs))
  let K := e.symm '' closedBall (e x) d
  have compact : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono sub)
  refine ⟨d/4,by positivity,?_⟩
  rw [show 4*(d/4)=d by ring]
  refine ⟨sub,(exhaust K compact).mono fun i cover => ?_⟩
  have inside (w : ℂ) (hw : w∈ball (e x) d) : e.symm w∈U i := cover (mem_image_of_mem _ (ball_subset_closedBall hw))
  refine ⟨fun w hw => ?_,(inj i).comp (e.symm.injOn.mono (ball_subset_closedBall.trans sub)) inside⟩
  exact (((hol i).contMDiffAt ((op i).mem_nhds (inside w hw))).comp w
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x)
      (sub (ball_subset_closedBall hw)))).contDiffAt.analyticAt

/-- A local bound on values over one patch also bounds the
derivative at its center by the elementary disk Schwarz estimate. -/
theorem bounded_chart_center_derivative {ι : Type*} {l : Filter ι} {G : ι → ℂ → ℂ}
    {a : ℂ} {W : Set ℂ} (openAt : W∈𝓝 a) {C : ℝ}
    (values : ∀ᶠ i in l, ∀ z∈W, ‖G i z‖≤C) {V : Set ℂ} (vAt : V∈𝓝 a)
    (an : ∀ᶠ i in l, AnalyticOnNhd ℂ (G i) V) :
    ∃ B : ℝ, ∀ᶠ i in l, ‖G i a‖≤C ∧ ‖deriv (G i) a‖≤B := by
  obtain ⟨d,dp,sub⟩ := Metric.mem_nhds_iff.mp (inter_mem openAt vAt)
  let S := ball a d
  have aS : a∈S := mem_ball_self dp
  refine ⟨(2*C)/d,?_⟩
  filter_upwards [values,an] with i hi h
  have small (w : ℂ) (hw : w∈S) := hi w (sub hw).1
  refine ⟨small a aS,norm_deriv_le_div_of_mapsTo_ball (h.differentiableOn.mono (fun w hw => (sub hw).2)) ?_ dp⟩
  intro z hz
  apply mem_closedBall.mpr
  have tri := dist_triangle (G i z) 0 (G i a)
  rw [dist_zero_right,dist_zero_left] at tri
  linarith [small z hz,small a aS]

/-- Boundedness propagates over overlapping charts of a connected
Riemann surface. An exhaustion normalized at one point is therefore
bounded on each compact set, with no a priori bound on its images. -/
theorem normalized_univalent_exhaustion_bounded {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {l : Filter ι} {U : ι → Set M} {F : ι → M → ℂ}
    (op : ∀ i, IsOpen (U i)) (hol : ∀ i, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F i) (U i))
    (inj : ∀ i, InjOn (F i) (U i)) (exhaust : ∀ K : Set M, IsCompact K → ∀ᶠ i in l, K⊆U i)
    (p : M) (base : ∀ᶠ i in l, F i p=0 ∧ deriv (F i ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=1) :
    ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0<C ∧ ∀ᶠ i in l, K⊆U i ∧ ∀ z∈K, ‖F i z‖≤C := by
  classical
  obtain ⟨C,_,propagate⟩ := univalent_disk_values_from_nearby_jet
  let S := {x : M | ∃ V∈𝓝 x, ∃ B : ℝ, ∀ᶠ i in l, ∀ z∈V, ‖F i z‖≤B}
  have grow (x : M) {e : OpenPartialHomeomorph M ℂ} (xs : x∈e.source) {r : ℝ} (rp : 0<r)
      (charts : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i ∘ e.symm) (ball (e x) (4*r)) ∧
        InjOn (F i ∘ e.symm) (ball (e x) (4*r)))
      (a : ℂ) (ha : a∈ball (e x) r) (A B : ℝ)
      (jet : ∀ᶠ i in l, ‖F i (e.symm a)‖≤A ∧ ‖deriv (F i ∘ e.symm) a‖≤B) : x∈S := by
    let V := e.source ∩ e ⁻¹' ball (e x) r
    have vn : V∈𝓝 x := inter_mem (e.open_source.mem_nhds xs) ((e.continuousAt xs).preimage_mem_nhds (ball_mem_nhds _ rp))
    refine ⟨V,vn,A+B*Real.exp (2*C)*(2*r),?_⟩
    filter_upwards [charts,jet] with i hi ji
    intro z hz
    have h := propagate _ _ _ rp hi.1 hi.2 a ha (e z) hz.2
    simp only [comp_apply,e.left_inv hz.1] at h
    exact h.trans (add_le_add ji.1 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ji.2 (Real.exp_pos _).le) (by positivity)))
  have atP : p∈S := by
    obtain ⟨r,rp,_,ev⟩ := eventual_univalent_chart_disk op hol inj exhaust p
    apply grow p (mem_chart_source ℂ p) rp ev _ (mem_ball_self rp) 0 1
    filter_upwards [base] with i hi
    simp [((chartAt ℂ p).left_inv (mem_chart_source ℂ p)),hi.1,hi.2]
  have so : IsOpen S := isOpen_iff_mem_nhds.mpr fun x hx => by
    obtain ⟨V,vn,B,bd⟩ := hx
    apply mem_of_superset (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr vn))
    exact fun y hy => ⟨V,mem_interior_iff_mem_nhds.mp hy,B,bd⟩
  have sc : IsClosed S := isClosed_of_closure_subset (by
    intro x hx
    let e := chartAt ℂ x
    obtain ⟨r,rp,sub,ev⟩ := eventual_univalent_chart_disk op hol inj exhaust x
    have xs : x∈e.source := mem_chart_source ℂ x
    have near : e.source ∩ e ⁻¹' ball (e x) r∈𝓝 x :=
      inter_mem (e.open_source.mem_nhds xs) ((e.continuousAt xs).preimage_mem_nhds (ball_mem_nhds _ rp))
    obtain ⟨y,⟨ys,yr⟩,⟨V,vn,A,bd⟩⟩ := mem_closure_iff_nhds.mp hx _ near
    have yn : e.symm ⁻¹' V∈𝓝 (e y) := (e.symm.continuousAt (e.map_source ys)).preimage_mem_nhds (by rwa [e.left_inv ys])
    have ybig : e y∈ball (e x) (4*r) := ball_subset_ball (by linarith : r≤4*r) yr
    obtain ⟨B,bound⟩ := bounded_chart_center_derivative (G:=fun i => F i ∘ e.symm) yn
      (bd.mono fun i hi z hz => hi _ hz) (isOpen_ball.mem_nhds ybig) (ev.mono fun _ h => h.1)
    exact grow x xs rp ev (e y) yr A B bound)
  have full := (isClopen_iff.mp (show IsClopen S from ⟨sc,so⟩)).resolve_left (nonempty_of_mem atP).ne_empty
  have every (x : M) : x∈S := full.symm ▸ mem_univ x
  choose V vn B vb using every
  intro K compact
  obtain ⟨t,_,cov⟩ := compact.elim_nhds_subcover V (fun x _ => vn x)
  let bound := 1+∑ x∈t, |B x|
  have bp : 0<bound := by dsimp [bound]; positivity
  refine ⟨bound,bp,?_⟩
  have allBounds := (eventually_all_finset t).mpr (fun x _ => vb x)
  filter_upwards [allBounds,exhaust K compact] with i hb hi
  refine ⟨hi,?_⟩
  intro z hz
  obtain ⟨y,hy,hz'⟩ := mem_iUnion₂.mp (cov hz)
  have one := Finset.single_le_sum (f:=fun x => |B x|) (fun _ _ => abs_nonneg _) hy
  exact (hb y hy z hz').trans ((le_abs_self _).trans (by dsimp [bound]; linarith))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_univalent_exhaustion_bounded
