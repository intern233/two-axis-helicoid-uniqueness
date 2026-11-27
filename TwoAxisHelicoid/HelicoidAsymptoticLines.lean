import TwoAxisHelicoid.HelicoidAsymptoticContainment

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Metric
open scoped Topology
set_option maxHeartbeats 1300000

theorem affine_ray_norm_tendsto_atTop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B W : E) (hW : W ≠ 0) :
    Tendsto (fun n : ℕ => ‖B+((n:ℝ)+1) • W‖) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => ((n:ℝ)+1)*‖W‖-‖B‖) atTop atTop :=
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-‖B‖) (hn.atTop_mul_const (norm_pos_iff.mpr hW))
  apply tendsto_atTop_mono _ hh
  intro n
  have ht := norm_sub_norm_le (((n:ℝ)+1) • W) (-B)
  rw [norm_smul,Real.norm_of_nonneg (by positivity),norm_neg,sub_neg_eq_add] at ht
  simpa only [add_comm B] using ht

theorem affine_ray_normalized_coordinate_limit (B W : Fin 3 → ℝ)
    {q : ℕ → Fin 3 → ℝ}
    (hq : Tendsto (fun n : ℕ => q n-(B+((n:ℝ)+1) • W)) atTop (𝓝 0)) (j : Fin 3) :
    Tendsto (fun n : ℕ => (q n j)/((n:ℝ)+1)) atTop (𝓝 (W j)) := by
  have hcoord : Tendsto (fun n : ℕ => q n j-(B j+((n:ℝ)+1)*(W j))) atTop (𝓝 0) :=
    (continuous_apply j).continuousAt.tendsto.comp hq
  have hn := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := ((hcoord.add (tendsto_const_nhds (x := B j))).mul hn).add (tendsto_const_nhds (x := W j))
  simp only [zero_add,mul_zero] at hh
  apply hh.congr'
  filter_upwards with n
  have hne : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem normalized_helicoid_side_identity {α : ℝ} {P : Fin 3 → ℝ}
    (h : P ∈ range (axisRuledHelicoid I α 0)) :
    P 0*Real.sin (α*P 2) = P 1*Real.cos (α*P 2) := by
  obtain ⟨w,rfl⟩ := h
  rw [axisRuledHelicoid_standard_ruling]
  change w.re*Real.cos (α*w.im)*Real.sin (α*w.im) = w.re*Real.sin (α*w.im)*Real.cos (α*w.im)
  ring

/-- A complete affine line approaching a vertical helicoid at infinity
cannot be oblique. The argument uses only positional C⁰ closeness and
two constant-height-phase sequences. -/
theorem line_approaching_helicoid_horizontal_or_vertical {S : Set (Fin 3 → ℝ)}
    {α : ℝ} (hα : α ≠ 0) (h : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (A V : Fin 3 → ℝ) (hline : ∀ t : ℝ, A+t • V ∈ S) :
    V 2 = 0 ∨ V 0 = 0 ∧ V 1 = 0 := by
  by_cases hz : V 2 = 0
  · exact Or.inl hz
  right
  let s := 2*Real.pi/(α*V 2)
  have hs : s ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (mul_ne_zero hα hz)
  let W := s • V
  have hW : W ≠ 0 := by
    intro hh
    have h2 : s*V 2 = 0 := congrFun hh 2
    exact (mul_ne_zero hs hz) h2
  have hall (θ : ℝ) : W 0*Real.sin θ = W 1*Real.cos θ := by
    let t := (θ/α-A 2)/V 2
    let B := A+t • V
    let p := fun n : ℕ => B+((n:ℝ)+1) • W
    have hp (n : ℕ) : p n ∈ S := by
      have he : p n = A+(t+((n:ℝ)+1)*s) • V := by
        dsimp only [p,B,W]
        rw [add_smul t ((n+1:ℝ)*s),mul_smul,add_assoc]
      rw [he]
      exact hline _
    have phase (n : ℕ) : α*p n 2 = θ+(n+1:ℕ)*(2*Real.pi) := by
      change α*(A 2+t*V 2+((n:ℝ)+1)*(s*V 2)) = _
      simp only [Nat.cast_add,Nat.cast_one]
      dsimp only [t,s]
      field_simp
      ring
    obtain ⟨q,hq,hnear⟩ := h.exists_sequence (range_nonempty _) hp (affine_ray_norm_tendsto_atTop B W hW)
    have hd : Tendsto (fun n : ℕ => q n 2-p n 2) atTop (𝓝 0) :=
      (continuous_apply (2 : Fin 3)).continuousAt.tendsto.comp hnear
    let f := fun n : ℕ => α*(q n 2-p n 2)+θ
    have hf : Tendsto f atTop (𝓝 θ) := by
      simpa [f] using ((tendsto_const_nhds (x := α)).mul hd).add (tendsto_const_nhds (x := θ))
    have hphase (n : ℕ) : α*q n 2 = f n+(n+1:ℕ)*(2*Real.pi) := by
      dsimp only [f]
      linarith only [phase n]
    have heq (n : ℕ) : (q n 0/((n:ℝ)+1))*Real.sin (f n) = (q n 1/((n:ℝ)+1))*Real.cos (f n) := by
      have he := normalized_helicoid_side_identity (hq n)
      rw [hphase,Real.sin_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi] at he
      field_simp
      exact he
    have hx := (affine_ray_normalized_coordinate_limit B W hnear 0).mul (Real.continuous_sin.continuousAt.tendsto.comp hf)
    have hy := (affine_ray_normalized_coordinate_limit B W hnear 1).mul (Real.continuous_cos.continuousAt.tendsto.comp hf)
    exact tendsto_nhds_unique hx (hy.congr fun n => (heq n).symm)
  have h₁ := hall 0
  have h₀ := hall (Real.pi/2)
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one] at h₁
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_zero,mul_one] at h₀
  exact ⟨(mul_eq_zero.mp h₀).resolve_left hs,(mul_eq_zero.mp h₁.symm).resolve_left hs⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.line_approaching_helicoid_horizontal_or_vertical
