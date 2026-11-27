import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

private theorem unit_distance_to_real_pole {z : ℂ} (unit : ‖z‖=1) (hr : 0≤z.re) :
    ‖z-1‖≤2*|z.im| := by
  have sq : z.re*z.re+z.im*z.im=1 := by
    change normSq z=1
    rw [normSq_eq_norm_sq,unit,one_pow]
  have upper : z.re≤1 := unit ▸ re_le_norm z
  have diff : |z.re-1|≤|z.im| := by
    rw [abs_of_nonpos (by linarith)]
    nlinarith [sq_abs z.im,abs_nonneg z.im,mul_nonneg hr (sub_nonneg.mpr upper)]
  calc ‖z-1‖ ≤ |(z-1).re|+|(z-1).im| := norm_le_abs_re_add_abs_im _
    _ ≤ 2*|z.im| := by simp only [sub_re,one_re,sub_im,one_im,sub_zero]; linarith

/-- A continuous unit direction on a convex domain approaching a real
line in angle has a single one-sided real unit limit at any boundary
point. Connectedness of small neighborhoods selects the sign. -/
theorem unit_direction_limit_on_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (cv : Convex ℝ S) {f : E → ℂ} (cf : ContinuousOn f S)
    (unit : ∀ x ∈ S, ‖f x‖=1) {p : E} (hi : Tendsto (fun x => (f x).im) (𝓝[S] p) (𝓝 0)) :
    ∃ c : ℂ, (c=1 ∨ c= -1) ∧ Tendsto f (𝓝[S] p) (𝓝 c) := by
  have imBound : ∀ᶠ x in 𝓝[S] p, |(f x).im|<1/2 := by
    exact hi.abs.eventually_lt_const (by norm_num : |(0:ℝ)|<1/2)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhdsWithin_iff.mp imBound
  let U := ball p r ∩ S
  have connected : IsPreconnected U := ((convex_ball p r).inter cv).isPreconnected
  have near : ∀ᶠ x in 𝓝[S] p, x ∈ U := inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p hr)) self_mem_nhdsWithin
  have nz (x : E) (hx : x ∈ U) : (f x).re ≠ 0 := by
    intro eq
    have sq : (f x).re*(f x).re+(f x).im*(f x).im=1 := by
      change normSq (f x)=1
      rw [normSq_eq_norm_sq,unit x hx.2,one_pow]
    have bound : |(f x).im|<1/2 := hsub hx
    rw [eq,zero_mul,zero_add] at sq
    nlinarith [sq_abs (f x).im,abs_nonneg (f x).im]
  have sign : (∀ x ∈ U, 0≤(f x).re) ∨ (∀ x ∈ U, (f x).re≤0) := by
    by_cases h : ∀ x ∈ U, 0≤(f x).re
    · exact Or.inl h
    push Not at h
    obtain ⟨a,ha,neg⟩ := h
    refine Or.inr fun x hx => ?_
    by_contra! pos
    have cc := (Complex.continuous_re.comp_continuousOn cf).mono (show U⊆S from inter_subset_right)
    obtain ⟨v,hv,e⟩ := connected.intermediate_value ha hx cc (show (0:ℝ) ∈ Icc (f a).re (f x).re from ⟨neg.le,pos.le⟩)
    exact nz v hv e
  have closer {g : E → ℂ} (sg : ∀ x ∈ U, 0≤(g x).re) (gu : ∀ x ∈ U, ‖g x‖=1)
      (gi : Tendsto (fun x => (g x).im) (𝓝[S] p) (𝓝 0)) : Tendsto g (𝓝[S] p) (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have small := (Metric.tendsto_nhds.mp gi) (ε/2) (half_pos hε)
    filter_upwards [near,small] with x hx close
    rw [Real.dist_eq,sub_zero] at close
    rw [dist_eq_norm]
    exact (unit_distance_to_real_pole (gu x hx) (sg x hx)).trans_lt (by linarith)
  rcases sign with pos | neg
  · exact ⟨1,Or.inl rfl,closer pos (fun x hx => unit x hx.2) hi⟩
  · have im' : Tendsto (fun x => (-f x).im) (𝓝[S] p) (𝓝 0) := by simpa using hi.neg
    have res := closer (g := fun x => -f x) (fun x hx => by simpa using neg x hx)
      (fun x hx => by simpa using unit x hx.2) im'
    exact ⟨-1,Or.inr rfl,by simpa only [neg_neg] using res.neg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unit_direction_limit_on_convex
