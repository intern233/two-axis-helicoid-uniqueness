import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A locally uniform limit of zero-free holomorphic functions which
vanishes at an interior point must vanish in a neighborhood. We apply
the maximum principle to reciprocals on a small surrounding circle. -/
theorem zero_free_holomorphic_limit_local {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (op : IsOpen U)
    (conv : TendstoLocallyUniformlyOn F f l U)
    (ev : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ ∀ z∈U, F i z≠0)
    {x : ℂ} (hx : x∈U) (van : f x=0) : ∀ᶠ y in 𝓝 x, f y=0 := by
  have df := conv.differentiableOn (ev.mono fun _ h => h.1) op
  rcases (df.analyticAt (op.mem_nhds hx)).eventually_eq_zero_or_eventually_ne_zero with eq|isolated
  · exact eq
  exfalso
  have nb : ∀ᶠ z in 𝓝 x, z∈U ∧ (z≠x → f z≠0) := by
    filter_upwards [op.mem_nhds hx,eventually_nhdsWithin_iff.mp isolated] with z hz h using ⟨hz,h⟩
  obtain ⟨r,rp,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp nb
  have inU : closedBall x r⊆U := fun _ h => (sub h).1
  have nz (z : ℂ) (hz : z∈sphere x r) : f z≠0 := (sub (sphere_subset_closedBall hz)).2 (by
    rintro rfl
    exact rp.ne' (by simpa using (mem_sphere.mp hz).symm))
  obtain ⟨a,ha,small⟩ := (isCompact_sphere x r).exists_isMinOn (NormedSpace.sphere_nonempty.mpr rp.le)
    (df.continuousOn.norm.mono (sphere_subset_closedBall.trans inU))
  let δ := ‖f a‖/2
  have pos : 0<δ := half_pos (norm_pos_iff.mpr (nz a ha))
  have uniform := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere x r)).mp
    (conv.mono (sphere_subset_closedBall.trans inU))
  have lower : ∀ᶠ i in l, δ≤‖F i x‖ := by
    filter_upwards [ev,Metric.tendstoUniformlyOn_iff.mp uniform δ pos] with i hi close
    have inner := (hi.1.diffContOnCl_ball inU).inv (fun z hz => hi.2 z (inU (closure_ball_subset_closedBall hz)))
    have mx := norm_le_of_forall_mem_frontier_norm_le isBounded_ball inner (C:=δ⁻¹) (fun z h => by
      rw [frontier_ball x rp.ne'] at h
      change ‖(F i z)⁻¹‖≤δ⁻¹
      rw [norm_inv]
      apply inv_anti₀ pos
      have diff := norm_sub_norm_le (f z) (F i z)
      rw [← dist_eq_norm] at diff
      have minval : ‖f a‖≤‖f z‖ := small h
      dsimp [δ] at *
      linarith [close z h]) (subset_closure (mem_ball_self rp))
    change ‖(F i x)⁻¹‖≤δ⁻¹ at mx
    rwa [norm_inv,inv_le_inv₀ (norm_pos_iff.mpr (hi.2 x hx)) pos] at mx
  have low := ge_of_tendsto (conv.tendsto_at hx).norm lower
  rw [van,norm_zero] at low
  exact pos.not_ge low

/-- A locally uniform limit of injective holomorphic maps on a
connected domain is injective as soon as the limit is nonconstant. -/
theorem nonconstant_univalent_limit_injective {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (op : IsOpen U) (conn : IsPreconnected U)
    (conv : TendstoLocallyUniformlyOn F f l U) (ev : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U ∧ InjOn (F i) U)
    (non : ∀ b : ℂ, ¬ EqOn f (fun _ => b) U) : InjOn f U := by
  intro x hx y hy eq
  by_contra ne
  let V := U ∩ {x}ᶜ
  have ov : IsOpen V := op.inter isOpen_ne
  have yv : y∈V := ⟨hy,Ne.symm ne⟩
  let G := fun i z => F i z-F i x
  let g := fun z => f z-f x
  have uniform : TendstoLocallyUniformlyOn G g l V := by
    apply Metric.tendstoLocallyUniformlyOn_iff.mpr
    intro ε ep z hz
    obtain ⟨S,sn,s⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp (conv.mono (inter_subset_left (s:=U) (t:={x}ᶜ))) (ε/2) (half_pos ep) z hz
    refine ⟨S,sn,?_⟩
    filter_upwards [s,Metric.tendsto_nhds.mp (conv.tendsto_at hx) (ε/2) (half_pos ep)] with i close base
    intro w hw
    have triangle := dist_sub_sub_le (f w) (f x) (F i w) (F i x)
    change dist (f w-f x) (F i w-F i x)<ε
    linarith [close w hw,dist_comm (f x) (F i x)]
  have eqN := zero_free_holomorphic_limit_local ov uniform (ev.mono fun i h => by
    refine ⟨(h.1.mono inter_subset_left).sub_const _,fun w hw => sub_ne_zero.mpr (fun equal => hw.2 (h.2 hw.1 hx equal))⟩)
    yv (sub_eq_zero.mpr eq.symm)
  have an := (conv.differentiableOn (ev.mono fun _ h => h.1) op).analyticOnNhd op
  exact non (f x) (an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const conn hy (eqN.mono fun _ h => sub_eq_zero.mp h))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.zero_free_holomorphic_limit_local
#print axioms TwoAxisHelicoid.nonconstant_univalent_limit_injective
