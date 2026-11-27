import TwoAxisHelicoid.HeightEndFarCone

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1200000

/-- In each far horizontal level the angular cone may be centered at a
horizontal offset tending to zero. The bounded-height part has uniformly
bounded initial data and needs no offset. -/
theorem height_end_asymptotic_axis_cones
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (α R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0))
    (h₀ : Tendsto (fun x : ℝ => X (x:ℂ) 0) (cobounded ℝ) (𝓝 0))
    (h₁ : Tendsto (fun x : ℝ => X (x:ℂ) 1) (cobounded ℝ) (𝓝 0))
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T < ‖z‖ →
      ∃ b : Fin 3 → ℝ, |b 0| ≤ ε ∧ |b 1| ≤ ε ∧ b 2 = 0 ∧
        |endHorizontalTransverse (α*z.re) (X z-b)| ≤ κ*|endHorizontalSupport (α*z.re) (X z-b)| := by
  let δ := min (κ/3) (1/2)
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδκ : 3*δ ≤ κ := by dsimp [δ]; linarith [min_le_left (κ/3) (1/2 : ℝ)]
  have hsmall : ∀ᶠ z : ℂ in cobounded ℂ, ‖F z‖ < δ := by
    simpa only [Metric.mem_ball,dist_zero_right] using hF.eventually (Metric.ball_mem_nhds 0 hδ0)
  obtain ⟨S,_hS,hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hsmall
  let Y := max (S+1) (max (R₀+1) 1)
  have hY : 0 < Y := by
    have hh := (le_max_right (R₀+1) 1).trans (le_max_right (S+1) (max (R₀+1) 1))
    dsimp [Y]
    linarith
  have hRY : R₀ < Y := by
    have hh := (le_max_left (R₀+1) 1).trans (le_max_right (S+1) (max (R₀+1) 1))
    dsimp [Y]
    linarith
  have hSY : S ≤ Y := by dsimp [Y]; linarith [le_max_left (S+1) (max (R₀+1) 1)]
  have hphase z (hz : Y ≤ ‖z‖) : |(F z).im| ≤ δ :=
    (Complex.abs_im_le_norm (F z)).trans (hS (hSY.trans hz)).le
  have hd z (hz : Y ≤ ‖z‖) := hX z (hRY.trans_le hz)
  have near : ∀ᶠ x : ℝ in cobounded ℝ, |X (x:ℂ) 0| < ε ∧ |X (x:ℂ) 1| < ε := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using
      (h₀.eventually (Metric.ball_mem_nhds 0 hε)).and (h₁.eventually (Metric.ball_mem_nhds 0 hε))
  obtain ⟨A,_,hA⟩ := hasBasis_cobounded_norm.eventually_iff.mp near
  let B := max Y (A+1)
  have hYB : Y ≤ B := le_max_left _ _
  have hAB : A < B := by dsimp [B]; linarith [le_max_right Y (A+1)]
  have hB : 0 < B := hY.trans_le hYB
  have hnp (x : ℝ) : Y ≤ ‖(x : ℂ)+I*Y‖ := by
    simpa only [abs_of_pos hY] using vertical_line_norm_ge_abs x Y
  have hnm (x : ℝ) : Y ≤ ‖(x : ℂ)+I*((-Y : ℝ) : ℂ)‖ := by
    simpa only [abs_neg,abs_of_pos hY] using vertical_line_norm_ge_abs x (-Y)
  have hcp : Continuous (fun x : ℝ => X ((x : ℂ)+I*Y)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hd _ (hnp x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*Y) (by fun_prop)
  have hcm : Continuous (fun x : ℝ => X ((x : ℂ)+I*((-Y : ℝ) : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hd _ (hnm x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*((-Y : ℝ) : ℂ)) (by fun_prop)
  obtain ⟨Cp,hCp,hpBound⟩ := ((isCompact_Icc (a := -B) (b := B)).image hcp).isBounded.exists_pos_norm_le
  obtain ⟨Cm,hCm,hmBound⟩ := ((isCompact_Icc (a := -B) (b := B)).image hcm).isBounded.exists_pos_norm_le
  let C := 2*(Cp+Cm)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpC : 2*Cp ≤ C := by dsimp [C]; linarith
  have hmC : 2*Cm ≤ C := by dsimp [C]; linarith
  have hbase (x : ℝ) (hx : |x| ≤ B) (s : ℝ) (hs : s ∈ ({-Y,Y} : Set ℝ)) :
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*s))| ≤ C ∧
      |endHorizontalTransverse (α*x) (X ((x : ℂ)+I*s))| ≤ C := by
    have hxm : x ∈ Icc (-B) B := abs_le.mp hx
    simp only [mem_insert_iff,mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · have hb := hmBound _ ⟨x,hxm,rfl⟩
      have hv j : |X ((x : ℂ)+I*((-Y : ℝ) : ℂ)) j| ≤ Cm := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ j).trans hb
      exact ⟨(endHorizontalSupport_bound _ (hv 0) (hv 1)).trans hmC,
        (endHorizontalTransverse_bound _ (hv 0) (hv 1)).trans hmC⟩
    · have hb := hpBound _ ⟨x,hxm,rfl⟩
      have hv j : |X ((x : ℂ)+I*Y) j| ≤ Cp := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ j).trans hb
      exact ⟨(endHorizontalSupport_bound _ (hv 0) (hv 1)).trans hpC,
        (endHorizontalTransverse_bound _ (hv 0) (hv 1)).trans hpC⟩
  let V := Y+2*C+6*C/δ+1
  have hYV : Y ≤ V := by
    have hh : 0 ≤ 6*C/δ := div_nonneg (by positivity) hδ0.le
    dsimp [V]
    linarith
  refine ⟨B+V,by linarith,?_⟩
  intro z hz
  have he : (z.re : ℂ)+I*z.im = z := by simpa only [mul_comm] using Complex.re_add_im z
  by_cases hx : B < |z.re|
  · have hn (s : ℝ) : Y ≤ ‖(z.re : ℂ)+I*s‖ := by
      have hh := Complex.abs_re_le_norm ((z.re : ℂ)+I*s)
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] at hh
      exact hYB.trans (hx.le.trans hh)
    let b : Fin 3 → ℝ := ![X (z.re:ℂ) 0,X (z.re:ℂ) 1,0]
    have hsmallb := hA (show A ≤ ‖z.re‖ from (hAB.trans hx).le)
    refine ⟨b,hsmallb.1.le,hsmallb.2.le,rfl,?_⟩
    have hh := height_end_axis_level_cone (X := fun w => X w-b) α z.re z.im δ hδ0.le hδ
      (fun s => (hd _ (hn s)).sub_const b) (fun s => hphase _ (hn s))
      ⟨by simp [b],by simp [b]⟩
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 2*δ ≤ κ) (abs_nonneg _))
  · have hxB : |z.re| ≤ B := le_of_not_gt hx
    have hnorm : ‖z‖ ≤ |z.re|+|z.im| := by
      calc ‖z‖ = ‖(z.re : ℂ)+I*z.im‖ := by rw [he]
           _ ≤ ‖(z.re : ℂ)‖+‖I*z.im‖ := norm_add_le _ _
           _ = _ := by simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    have hyV : V < |z.im| := by linarith
    have hfar : 3*C ≤ δ*((|z.im|-Y)/2-C) := by
      have hm := mul_le_mul_of_nonneg_left hyV.le hδ0.le
      have hcdiv : δ*(6*C/δ) = 6*C := by field_simp
      dsimp [V] at hm
      nlinarith
    have hh := height_end_far_vertical_cone α z.re Y C δ z.im hC hδ0.le hδ hd hphase
      (hbase z.re hxB) (hYV.trans hyV.le) hfar
    rw [he] at hh
    refine ⟨0,by simpa using hε.le,by simpa using hε.le,rfl,?_⟩
    simpa only [sub_zero] using hh.trans (mul_le_mul_of_nonneg_right hδκ (abs_nonneg _))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_end_asymptotic_axis_cones
