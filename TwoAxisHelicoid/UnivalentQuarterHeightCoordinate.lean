import TwoAxisHelicoid.RhombicQuarterHeight
import TwoAxisHelicoid.ActualComplexHeight

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A holomorphic function whose derivative has positive real part on
a convex set has positive real part on every normalized secant. -/
theorem positive_real_secant_of_derivative {U : Set ℂ} (conv : Convex ℝ U)
    {f f' : ℂ → ℂ} (df : ∀ z∈U, HasDerivAt f (f' z) z) (pos : ∀ z∈U, 0<(f' z).re)
    {z w : ℂ} (hz : z∈U) (hw : w∈U) (ne : w≠z) :
    0<((f w-f z)/(w-z)).re := by
  let v := w-z
  let γ := fun s : ℝ => z+(s:ℂ)*v
  let F := fun s : ℝ => ((f (γ s)-f z)/v).re
  have vn : v≠0 := sub_ne_zero.mpr ne
  have inside (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : γ s∈U := by
    simpa only [γ,v,Complex.real_smul] using conv.add_smul_sub_mem hz hw hs
  have dg (s : ℝ) : HasDerivAt γ v s := by
    simpa [γ] using (((hasDerivAt_id s).ofReal_comp.mul_const v).const_add z)
  have der (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt F (f' (γ s)).re s := by
    have h := (((df _ (inside s hs)).scomp s (dg s)).sub_const (f z)).div_const v
    have d := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
    simpa [F,Function.comp_def,smul_eq_mul,mul_div_cancel_left₀ _ vn] using! d
  have inc : StrictMonoOn F (Icc 0 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun s h => (der s h).continuousAt.continuousWithinAt)
      (fun s h => (der s (interior_subset h)).deriv.symm ▸ pos _ (inside s (interior_subset h)))
  have low := inc (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) zero_lt_one
  simpa [F,γ,v] using low

/-- The literal complex height is a global holomorphic coordinate on
the full open parameter rectangle. The proof uses only the marked
height differential and is independent of global embeddedness. -/
theorem actual_complex_height_univalent_quarter {t a : ℝ} (ht : 0<t) :
    let U := complexOpenRect 0 1 0 t
    let f := actualComplexHeight t a 1 ht
    (∀ z∈U, 0<(deriv f z).re) ∧
      (∀ z∈U, ∀ w∈U, w≠z → 0<((f w-f z)/(w-z)).re) ∧ InjOn f U := by
  intro U f
  let v := fun z => coordinateData t a 1 ht z 2
  have d (z : ℂ) (h : z∈U) : HasDerivAt f (v z) z :=
    actualComplexHeight_hasDerivAt ht (rhombic_horizontal_strip_not_mem ht h.2)
  have pos (z : ℂ) (h : z∈U) : 0<(v z).re := by
    have eq : (z.re:ℂ)+I*z.im=z := by apply Complex.ext <;> simp
    have s := rhombic_weierstrassP_quarter_im_neg ht h.1 h.2
    rw [eq] at s
    simpa [v,coordinateData,Complex.mul_re,rhombic_weierstrassP_real ht a] using s
  have sec := fun {z w : ℂ} (hz : z∈U) (hw : w∈U) (ne : w≠z) =>
    positive_real_secant_of_derivative (complexOpenRect_convex 0 1 0 t) d pos hz hw ne
  refine ⟨fun z hz => (d z hz).deriv.symm ▸ pos z hz,fun _ hz _ hw ne => sec hz hw ne,?_⟩
  intro z hz w hw eq
  by_contra ne
  have h := sec hw hz ne
  simp [eq] at h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_complex_height_univalent_quarter
