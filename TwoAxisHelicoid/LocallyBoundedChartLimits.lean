import TwoAxisHelicoid.HolomorphicDiskNormalFamily
import TwoAxisHelicoid.HolomorphicSurfaceIdentity

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology ContDiff Manifold

/-- A bounded holomorphic family on a fixed open chart converges
locally uniformly along an ultrafilter as soon as its point limits
are prescribed. The bound can depend on the chart. -/
theorem bounded_chart_limit_of_point_limits {ι : Type*} (l : Ultrafilter ι) (F : ι → ℂ → ℂ)
    {f : ℂ → ℂ} {U : Set ℂ} (op : IsOpen U) {C : ℝ} (cp : 0<C)
    (ev : ∀ᶠ i in (l : Filter ι), DifferentiableOn ℂ (F i) U ∧ ∀ x∈U, ‖F i x‖≤C)
    (lim : ∀ x∈U, Tendsto (fun i => F i x) (l : Filter ι) (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f (l : Filter ι) U ∧ AnalyticOnNhd ℂ f U := by
  let G := fun i x => F i x/(C:ℂ)
  have nz : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr cp.ne'
  obtain ⟨g,conv,_,_⟩ := bounded_holomorphic_disk_normal_limit l G (U:=U) (by
    intro x hx
    obtain ⟨r,rp,sub⟩ := Metric.isOpen_iff.mp op x hx
    refine ⟨r,rp,sub,ev.mono fun i hi => ⟨((hi.1.mono sub).div_const _),fun w hw => ?_⟩⟩
    apply mem_closedBall_zero_iff.mpr
    rw [show G i w=F i w/(C:ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_of_nonneg cp.le]
    exact (div_le_one cp).mpr (hi.2 w (sub hw)))
  have eq : EqOn g (fun x => f x/(C:ℂ)) U := fun x hx =>
    tendsto_nhds_unique (conv.tendsto_at hx) ((lim x hx).div_const _)
  have uniform := ((ContinuousLinearMap.lsmul ℂ ℂ (C:ℂ)).uniformContinuous).comp_tendstoLocallyUniformlyOn
    (conv.congr_right eq)
  have unscale (z : ℂ) : (C:ℂ)*(z/(C:ℂ))=z := by field_simp
  have actual : TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
    apply (uniform.congr (fun i z _ => unscale (F i z))).congr_right (fun z _ => unscale (f z))
  exact ⟨actual,(actual.differentiableOn (ev.mono fun _ h => h.1) op).analyticOnNhd op⟩

/-- Locally bounded holomorphic functions on domains exhausting an
abstract Riemann surface have one common holomorphic limit on the
entire surface. Convergence holds in each of the original charts. -/
theorem exhausting_surface_holomorphic_normal_limit {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (l : Ultrafilter ι) (U : ι → Set M) (F : ι → M → ℂ)
    (op : ∀ i, IsOpen (U i)) (hol : ∀ i, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F i) (U i))
    (bounded : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0<C ∧
      ∀ᶠ i in (l : Filter ι), K⊆U i ∧ ∀ z∈K, ‖F i z‖≤C) :
    ∃ f : M → ℂ, ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧
      (∀ x, Tendsto (fun i => F i x) (l : Filter ι) (𝓝 (f x))) ∧
      ∀ x : M, ∃ r : ℝ, 0<r ∧ closedBall (chartAt ℂ x x) r⊆(chartAt ℂ x).target ∧
        TendstoLocallyUniformlyOn (fun i => F i ∘ (chartAt ℂ x).symm) (f ∘ (chartAt ℂ x).symm)
          (l : Filter ι) (ball (chartAt ℂ x x) r) := by
  classical
  have pt (x : M) : ∃ y : ℂ, Tendsto (fun i => F i x) (l : Filter ι) (𝓝 y) := by
    obtain ⟨C,_,ev⟩ := bounded {x} isCompact_singleton
    obtain ⟨y,_,h⟩ := (isCompact_closedBall (0:ℂ) C).ultrafilter_le_nhds' (l.map fun i => F i x)
      (ev.mono fun _ hi => mem_closedBall_zero_iff.mpr (hi.2 x (mem_singleton x)))
    exact ⟨y,h⟩
  choose f limit using pt
  have localChart (x : M) :
      ∃ r : ℝ, 0<r ∧ closedBall (chartAt ℂ x x) r⊆(chartAt ℂ x).target ∧
      TendstoLocallyUniformlyOn (fun i => F i ∘ (chartAt ℂ x).symm) (f ∘ (chartAt ℂ x).symm)
        (l : Filter ι) (ball (chartAt ℂ x x) r) ∧
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    let e := chartAt ℂ x
    have xs : x∈e.source := mem_chart_source ℂ x
    obtain ⟨r,rp,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source xs))
    let K := e.symm '' closedBall (e x) r
    have comp : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono sub)
    obtain ⟨C,cp,ev⟩ := bounded K comp
    obtain ⟨conv,an⟩ := bounded_chart_limit_of_point_limits l (fun i => F i ∘ e.symm) isOpen_ball cp
      (ev.mono fun i hi => by
        have inc (w : ℂ) (hw : w∈ball (e x) r) : e.symm w∈K := mem_image_of_mem _ (ball_subset_closedBall hw)
        refine ⟨fun w hw => ?_,fun w hw => hi.2 _ (inc w hw)⟩
        have h := ((hol i).contMDiffAt ((op i).mem_nhds (hi.1 (inc w hw)))).comp w
          (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x)
            (sub (ball_subset_closedBall hw)))
        exact h.contDiffAt.analyticAt.differentiableAt.differentiableWithinAt)
      (fun w _ => limit (e.symm w))
    exact ⟨r,rp,sub,conv,an _ (mem_ball_self rp)⟩
  refine ⟨f,?_,limit,fun x => ?_⟩
  · intro x
    obtain ⟨_,_,_,_,an⟩ := localChart x
    let e := chartAt ℂ x
    have xs : x∈e.source := mem_chart_source ℂ x
    apply (an.contDiffAt.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) xs)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds xs] with y hy using (congrArg f (e.left_inv hy)).symm
  · obtain ⟨r,rp,sub,conv,_⟩ := localChart x
    exact ⟨r,rp,sub,conv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exhausting_surface_holomorphic_normal_limit
