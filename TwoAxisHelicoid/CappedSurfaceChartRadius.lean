import TwoAxisHelicoid.UnivalentSurfaceCoordinate
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Truncated chart radius, extended continuously to the entire surface.
Every point below the cutoff is in the chart. -/
theorem continuous_capped_chart_radius {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M ℂ) (c : ℂ) {s : ℝ} (sp : 0<s) (dom : closedBall c s⊆e.target) :
    ∃ d : M → ℝ, Continuous d ∧ (∀ x, 0≤d x) ∧ (∀ x∈e.source, d x=min s ‖e x-c‖) ∧
      (∀ x, d x<s → x∈e.source ∧ d x=‖e x-c‖) ∧ ∀ x, d x=0 ↔ x=e.symm c := by
  classical
  let d := fun x => if x∈e.source then min s ‖e x-c‖ else s
  let K := e.symm '' closedBall c s
  have ck : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono dom)
  have sub : K⊆e.source := by rintro _ ⟨z,hz,rfl⟩; exact e.map_target (dom hz)
  have interior (x : M) (xs : x∈e.source) : d x=min s ‖e x-c‖ := ite_eq_left xs
  have out (x : M) (xo : x∉K) : d x=s := by
    by_cases xs : x∈e.source
    · rw [interior x xs,min_eq_left]
      apply le_of_not_gt
      intro lt
      exact xo ⟨e x,mem_closedBall.mpr (by simpa only [dist_eq_norm] using lt.le),e.left_inv xs⟩
    · exact ite_eq_right xs
  have low (x : M) (h : d x<s) : x∈e.source ∧ d x=‖e x-c‖ := by
    by_cases xs : x∈e.source
    · rw [interior x xs] at h ⊢
      exact ⟨xs,min_eq_right ((min_lt_iff.mp h).resolve_left (lt_irrefl _)).le⟩
    · exact (h.ne (ite_eq_right xs)).elim
  refine ⟨d,continuous_iff_continuousAt.mpr (fun x => ?_),fun x => ?_,interior,low,fun x => ?_⟩
  · by_cases xs : x∈e.source
    · have cont : ContinuousAt (fun y => min s ‖e y-c‖) x := continuousAt_const.min (((e.continuousAt xs).sub continuousAt_const).norm)
      apply cont.congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds xs] with z hz using interior z hz
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [ck.isClosed.isOpen_compl.mem_nhds (fun h => xs (sub h))] with z hz using out z hz
  · by_cases xs : x∈e.source
    · rw [interior x xs]; exact le_min sp.le (norm_nonneg _)
    · exact (show d x=s from ite_eq_right xs).symm ▸ sp.le
  · constructor
    · intro eq
      obtain ⟨xs,size⟩ := low x (eq.trans_lt sp)
      have point : e x=c := sub_eq_zero.mp (norm_eq_zero.mp (size.symm.trans eq))
      exact (e.left_inv xs).symm.trans (congrArg e.symm point)
    · rintro rfl
      have ht := dom (mem_closedBall_self sp.le)
      rw [interior _ (e.map_target ht),e.right_inv ht,sub_self,norm_zero,min_eq_right sp.le]

/-- The singular logarithms in two holomorphic coordinates differ by a
function with a finite limit, namely the log of the transition derivative. -/
theorem logarithmic_chart_radius_difference {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {e : OpenPartialHomeomorph M ℂ} (eh : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {p : M} (ps : p∈e.source) : ∃ C : ℝ,
    Tendsto (fun z => Real.log ‖e ((chartAt ℂ p).symm z)-e p‖-Real.log ‖z-chartAt ℂ p p‖)
      (𝓝[≠] (chartAt ℂ p p)) (𝓝 C) := by
  let a := chartAt ℂ p
  let c := a p
  let g := e ∘ a.symm
  let U := a.target ∩ a.symm ⁻¹' e.source
  have asrc : p∈a.source := mem_chart_source ℂ p
  have uc : c∈U := ⟨a.map_source asrc,by simpa only [mem_preimage,c,a.left_inv asrc] using ps⟩
  have op : IsOpen U := a.symm.continuousOn.isOpen_inter_preimage a.open_target e.open_source
  have an : AnalyticOnNhd ℂ g U := fun z hz => ((contMDiffAt_of_mem_maximalAtlas eh hz.2).comp z
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) p) hz.1)).contDiffAt.analyticAt
  have inj : InjOn g U := e.injOn.comp (a.symm.injOn.mono inter_subset_left) (fun _ h => h.2)
  have reg := univalent_analytic_deriv_ne_zero op an inj uc
  have diff := (an c uc).differentiableAt.hasDerivAt.tendsto_slope.norm
  refine ⟨_,((Real.continuousAt_log (norm_ne_zero_iff.mpr reg)).tendsto.comp diff).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (op.mem_nhds uc)] with z ne hz
  have nz : g z-g c≠0 := sub_ne_zero.mpr (fun eq => ne (inj hz uc eq))
  have size : ‖slope g c z‖=‖g z-g c‖/‖z-c‖ := by simpa only [slope,smul_eq_mul,inv_mul_eq_div,vsub_eq_sub] using (norm_div (g z-g c) (z-c))
  change Real.log ‖slope g c z‖=_
  rw [size,Real.log_div (norm_ne_zero_iff.mpr nz) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ne))]
  simp only [g,c,comp_apply,a.left_inv asrc,a]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.logarithmic_chart_radius_difference
