module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

public section

namespace TwoAxisHelicoid
open Set Filter MeasureTheory Topology
open scoped ContDiff Topology

private noncomputable def timePartial (F : ℝ × ℂ → ℝ) (q : ℝ × ℂ) : ℝ :=
  fderiv ℝ F q (1,0)

private theorem timePartial_hasDerivAt {F : ℝ × ℂ → ℝ} {s : ℝ} {z : ℂ}
    (h : DifferentiableAt ℝ F (s,z)) :
    HasDerivAt (fun r => F (r,z)) (timePartial F (s,z)) s :=
  h.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

private theorem compact_slice_derivative {F : ℝ × ℂ → ℝ} {s : ℝ} {K A : Set ℂ}
    (compact : IsCompact K) (meas : MeasurableSet A) (sub : A ⊆ K)
    (smooth : ∀ z ∈ K, ContDiffAt ℝ 1 F (s,z)) :
    HasDerivAt (fun r => ∫ z in A, F (r,z)) (∫ z in A, timePartial F (s,z)) s := by
  have regular : ∀ᶠ r in 𝓝 s, ∀ z∈K, ContDiffAt ℝ 1 F (r,z) :=
    compact.eventually_forall_of_forall_eventually
      (fun z hz => (smooth z hz).eventually (by norm_num))
  obtain ⟨ε,pos,near⟩ := Metric.mem_nhds_iff.mp regular
  let B := Metric.closedBall s (ε/2)
  have reg (r) (hr : r ∈ B) (z) (hz : z ∈ K) : ContDiffAt ℝ 1 F (r,z) :=
    near (show r ∈ Metric.ball s ε from lt_of_le_of_lt hr (half_lt_self pos)) z hz
  have cPartial (q : ℝ × ℂ) (hq : q ∈ B ×ˢ K) : ContinuousAt (timePartial F) q :=
    ((reg q.1 hq.1 q.2 hq.2).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have sectionF (r) (hr : r ∈ B) : ContinuousOn (fun z => F (r,z)) K :=
    fun z hz => ((reg r hr z hz).continuousAt.comp (f := fun w : ℂ => (r,w)) (by fun_prop)).continuousWithinAt
  have sectionD (r) (hr : r ∈ B) : ContinuousOn (fun z => timePartial F (r,z)) K :=
    fun z hz => ((cPartial (r,z) ⟨hr,hz⟩).comp (f := fun w : ℂ => (r,w)) (by fun_prop)).continuousWithinAt
  have center : s ∈ B := Metric.mem_closedBall_self (half_pos pos).le
  obtain ⟨L,bound⟩ := ((isCompact_closedBall s (ε/2)).prod compact).exists_bound_of_continuousOn
    (fun q hq => (cPartial q hq).continuousWithinAt)
  let μ := volume.restrict A
  have mF : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (fun z => F (r,z)) μ := by
    filter_upwards [Metric.ball_mem_nhds s (half_pos pos)] with r hr
    exact ((sectionF r (Metric.ball_subset_closedBall hr)).mono sub).aestronglyMeasurable meas
  have iF : Integrable (fun z => F (s,z)) μ := ((sectionF s center).integrableOn_compact compact).mono_set sub
  have mD : AEStronglyMeasurable (fun z => timePartial F (s,z)) μ :=
    ((sectionD s center).mono sub).aestronglyMeasurable meas
  have iL : Integrable (fun _ : ℂ => L) μ := integrableOn_const
    ((measure_mono sub).trans_lt compact.measure_lt_top).ne
  have bnd : ∀ᵐ z ∂μ, ∀ r ∈ Metric.ball s (ε/2), ‖timePartial F (r,z)‖ ≤ L := by
    filter_upwards [ae_restrict_mem meas] with z hz
    intro r hr
    exact bound (r,z) ⟨Metric.ball_subset_closedBall hr,sub hz⟩
  have hd : ∀ᵐ z ∂μ, ∀ r ∈ Metric.ball s (ε/2),
      HasDerivAt (fun v => F (v,z)) (timePartial F (r,z)) r := by
    filter_upwards [ae_restrict_mem meas] with z hz
    intro r hr
    exact timePartial_hasDerivAt ((reg r (Metric.ball_subset_closedBall hr) z (sub hz)).differentiableAt one_ne_zero)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z => F (r,z)) (F' := fun r z => timePartial F (r,z)) (μ := μ) (bound := fun _ => L)
    (Metric.ball_mem_nhds s (half_pos pos)) mF iF mD bnd iL hd).2

/-- Pass both time derivatives through the integral over any measurable subset of the compact patch. The joint C² germ over the patch gives the uniform bounds on a common time interval. -/
theorem compact_slice_integral_hessian {F : ℝ × ℂ → ℝ} {K A : Set ℂ}
    (compact : IsCompact K) (meas : MeasurableSet A) (sub : A ⊆ K)
    (smooth : ∀ z ∈ K, ContDiffAt ℝ 2 F (0,z)) :
    (∀ᶠ s in 𝓝 (0:ℝ), DifferentiableAt ℝ (fun r => ∫ z in A, F (r,z)) s) ∧
      HasDerivAt (deriv (fun r => ∫ z in A, F (r,z)))
        (∫ z in A, deriv (deriv (fun r => F (r,z))) 0) 0 := by
  have regular : ∀ᶠ s in 𝓝 (0:ℝ), ∀ z∈K, ContDiffAt ℝ 2 F (s,z) :=
    compact.eventually_forall_of_forall_eventually
      (fun z hz => (smooth z hz).eventually (by norm_num))
  have first := regular.mono (fun s hs => compact_slice_derivative compact meas sub
    (fun z hz => (hs z hz).of_le (show (1:ℕ∞ω) ≤ 2 by norm_num)))
  have dreg (z) (hz : z ∈ K) : ContDiffAt ℝ 1 (timePartial F) (0,z) :=
    ((smooth z hz).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have second := (compact_slice_derivative compact meas sub dreg).congr_of_eventuallyEq
    (first.mono fun _ h => h.deriv)
  refine ⟨first.mono (fun _ h => h.differentiableAt),?_⟩
  convert second using 1
  apply setIntegral_congr_fun meas
  intro z hz
  have localFirst : deriv (fun r => F (r,z)) =ᶠ[𝓝 (0:ℝ)] fun r => timePartial F (r,z) :=
    regular.mono fun _ h => (timePartial_hasDerivAt ((h z (sub hz)).differentiableAt (by norm_num))).deriv
  exact localFirst.deriv_eq.trans (timePartial_hasDerivAt ((dreg z (sub hz)).differentiableAt one_ne_zero)).deriv

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_slice_integral_hessian
