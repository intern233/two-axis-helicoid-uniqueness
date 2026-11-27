import TwoAxisHelicoid.HeightEndInjectivity

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- A decaying helicoidal correction forces actual embeddedness on some
closed subend. The proof uses monotonicity along height levels and the
properness already obtained from the same differential data. -/
theorem height_normalized_helicoidal_end_eventually_embedded
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (α b R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re+b)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) :
    ∃ R : ℝ, R₀ < R ∧ IsClosedEmbedding (fun z : {z : ℂ // R ≤ ‖z‖} => X z.1) := by
  obtain ⟨Y,hY,hRY,hsmall⟩ := helicoidal_correction_small_phase hF R₀
  have hnp (x : ℝ) : R₀ < ‖(x : ℂ)+I*Y‖ :=
    hRY.trans_le (by simpa [abs_of_pos hY] using vertical_line_norm_ge_abs x Y)
  have hnm (x : ℝ) : R₀ < ‖(x : ℂ)+I*(-Y)‖ :=
    hRY.trans_le (by simpa [abs_of_pos hY] using vertical_line_norm_ge_abs x (-Y))
  have hcp : Continuous (fun x : ℝ => X ((x : ℂ)+I*Y)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hX _ (hnp x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*Y) (by fun_prop)
  have hcm : Continuous (fun x : ℝ => X ((x : ℂ)+I*(-Y))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hX _ (hnm x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*(-Y)) (by fun_prop)
  obtain ⟨Cp,hCp,hpBound⟩ := ((isCompact_Icc (a := -Y) (b := Y)).image hcp).isBounded.exists_pos_norm_le
  obtain ⟨Cm,hCm,hmBound⟩ := ((isCompact_Icc (a := -Y) (b := Y)).image hcm).isBounded.exists_pos_norm_le
  let C := 2*(Cp+Cm)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase (x : ℝ) (hx : |x| ≤ Y) :
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*Y))| ≤ C ∧
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*(-Y)))| ≤ C := by
    have hxmem : x ∈ Icc (-Y) Y := abs_le.mp hx
    have hp := hpBound _ ⟨x,hxmem,rfl⟩
    have hm := hmBound _ ⟨x,hxmem,rfl⟩
    have hvp j : |X ((x : ℂ)+I*Y) j| ≤ Cp := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ j).trans hp
    have hvm j : |X ((x : ℂ)+I*(-Y)) j| ≤ Cm := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ j).trans hm
    have hsp := endHorizontalSupport_bound (α*x) (hvp 0) (hvp 1)
    have hsm := endHorizontalSupport_bound (α*x) (hvm 0) (hvm 1)
    exact ⟨hsp.trans (by dsimp [C]; linarith), hsm.trans (by dsimp [C]; linarith)⟩
  let R := max (R₀+1) (2*Y+2*C+1)
  have hR : R₀ < R := by dsimp [R]; linarith [le_max_left (R₀+1) (2*Y+2*C+1)]
  have hproper := height_normalized_helicoidal_end_isProperMap α b R₀ R hR hX hheight hF
  refine ⟨R,hR,IsClosedEmbedding.of_continuous_injective_isClosedMap hproper.continuous ?_ hproper.isClosedMap⟩
  intro z w he
  have hzn : R₀ < ‖z.1‖ := hR.trans_le z.2
  have hwn : R₀ < ‖w.1‖ := hR.trans_le w.2
  have hx : z.1.re = w.1.re := by
    have hh := congrFun he 2
    change X z.1 2 = X w.1 2 at hh
    rw [hheight z.1 hzn,hheight w.1 hwn] at hh
    linarith
  have hzcoord : (z.1.re : ℂ)+I*z.1.im = z.1 := by simpa [mul_comm] using Complex.re_add_im z.1
  have hwcoord : (z.1.re : ℂ)+I*w.1.im = w.1 := by rw [hx]; simpa [mul_comm] using Complex.re_add_im w.1
  have hy : z.1.im = w.1.im := by
    apply height_end_level_injective α z.1.re R₀ Y C hRY hC hX hsmall (hbase z.1.re)
    · rw [hzcoord]
      exact (le_max_right _ _).trans z.2
    · rw [hwcoord]
      exact (le_max_right _ _).trans w.2
    · rwa [hzcoord,hwcoord]
  exact Subtype.ext (Complex.ext hx hy)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_normalized_helicoidal_end_eventually_embedded
