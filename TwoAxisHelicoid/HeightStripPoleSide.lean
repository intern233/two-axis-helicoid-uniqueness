import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- On approach to the puncture from the left half-plane, finite
physical height forces the imaginary height to tend to positive
infinity, uniformly throughout any bounded range of physical heights. -/
theorem actual_height_pole_left_strip {t a : ℝ} (ht : 0<t) (W R : ℝ) :
    let H := actualComplexHeight t a 1 ht
    ∀ᶠ z in 𝓝[≠] (0:ℂ), z.re≤0 → |(H z).re|≤W → R < (H z).im := by
  intro H
  let f := actualHeightRegular t a 1 ht
  let M := ‖f 0‖+1
  have localBound : ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖<M :=
    (((actualHeightRegular_analyticAt_zero (a:=a) (c:=1) ht).continuousAt.norm).eventually
      (Iio_mem_nhds (show ‖f 0‖<M by dsimp [M]; linarith))).filter_mono nhdsWithin_le_nhds
  have large := (tendsto_norm_cobounded_atTop.comp (actualComplexHeight_tendsto (a:=a) ht (one_ne_zero : (1:ℝ)≠0))).eventually
    (eventually_gt_atTop (W+max M R))
  filter_upwards [localBound,large,rhombic_puncture_eventually_off_lattice ht] with z bound norm off
  intro left physical
  change W+max M R<‖H z‖ at norm
  have p : H z= -I/z+f z := by
    simpa [H,f,simplePoleCoordinate] using actualComplexHeight_principal_part (a:=a) (c:=1) ht off
  have pole : 0≤(-I/z).im := by
    rw [div_im]
    simp only [neg_im,I_im,neg_re,I_re,neg_zero,zero_mul,sub_zero,neg_one_mul,zero_div,sub_zero]
    exact div_nonneg (neg_nonneg.mpr left) (normSq_nonneg _)
  have low : -M<(H z).im := by
    rw [p,add_im]
    linarith [(abs_lt.mp ((abs_im_le_norm (f z)).trans_lt bound)).1]
  have ab : max M R < |(H z).im| := by linarith [norm_le_abs_re_add_abs_im (H z)]
  obtain alt|high := lt_abs.mp ab
  · linarith [le_max_right M R]
  · linarith [le_max_left M R]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_pole_left_strip
