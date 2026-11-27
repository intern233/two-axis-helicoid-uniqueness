module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter
open scoped ENNReal

/-- The two physical flux components in the scalar divergence equation. -/
@[expose] def planeMetricFlux (A B C : ℂ → ℝ) (z v : ℂ) : ℂ :=
  ⟨C z*v.re-B z*v.im, A z*v.im-B z*v.re⟩

private theorem flux_add (A B C : ℂ → ℝ) (z v w : ℂ) :
    planeMetricFlux A B C z (v+w)=planeMetricFlux A B C z v+planeMetricFlux A B C z w := by
  apply Complex.ext <;> simp [planeMetricFlux] <;> ring

private theorem flux_smul (A B C : ℂ → ℝ) (z v : ℂ) (r : ℝ) :
    planeMetricFlux A B C z (r • v)=r • planeMetricFlux A B C z v := by
  apply Complex.ext <;> simp [planeMetricFlux] <;> ring

theorem planeMetricFlux_norm_le (A B C : ℂ → ℝ) (z v : ℂ) :
    ‖planeMetricFlux A B C z v‖ ≤ (|C z|+2*|B z|+|A z|)*‖v‖ := by
  have bound (c t : ℝ) (ht : |t|≤‖v‖) : |c*t|≤|c| * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  calc
    _ ≤ |C z*v.re-B z*v.im|+|A z*v.im-B z*v.re| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|C z*v.re|+|B z*v.im|)+(|A z*v.im|+|B z*v.re|) :=
      add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ _ := by
      linarith [bound (C z) v.re (Complex.abs_re_le_norm _),bound (B z) v.im (Complex.abs_im_le_norm _),
        bound (A z) v.im (Complex.abs_im_le_norm _),bound (B z) v.re (Complex.abs_re_le_norm _)]

/-- Multiplication by the plane conductivity is a bounded operator on
actual square-integrable vector fields. Its action is pointwise a.e. -/
theorem exists_planeMetricFlux_L2 (μ : Measure ℂ) {A B C : ℂ → ℝ}
    (sa : Continuous A) (sb : Continuous B) (sc : Continuous C)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ T : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ,
      ∀ w : Lp ℂ 2 μ, ⇑(T w) =ᵐ[μ] (fun z => planeMetricFlux A B C z (w z)) := by
  let h := fun z => |C z|+2*|B z|+|A z|
  have sh : Continuous h := (sc.abs.add (continuous_const.mul sb.abs)).add sa.abs
  obtain ⟨M,hm⟩ := hk.bddAbove_image sh.continuousOn
  let L := max 2 M
  have bound (z v : ℂ) : ‖planeMetricFlux A B C z v‖≤L*‖v‖ := by
    apply (planeMetricFlux_norm_le A B C z v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases hz : z∈K
    · exact (hm ⟨z,hz,rfl⟩).trans (le_max_right _ _)
    · obtain ⟨e,f,g⟩ := off z hz
      simpa only [e,f,g,abs_one,abs_zero,mul_zero,add_zero,one_add_one_eq_two] using
        (show (2:ℝ)≤L from le_max_left _ _)
  have joint : Continuous (Function.uncurry (planeMetricFlux A B C)) := by
    change Continuous (Complex.equivRealProdCLM.symm ∘ (fun p : ℂ × ℂ =>
      (C p.1*p.2.re-B p.1*p.2.im,A p.1*p.2.im-B p.1*p.2.re)))
    apply Complex.equivRealProdCLM.symm.continuous.comp
    apply Continuous.prodMk <;> fun_prop (disch := assumption)
  have mem (w : Lp ℂ 2 μ) : MemLp (fun z => planeMetricFlux A B C z (w z)) 2 μ :=
    (Lp.memLp w).of_le_mul (joint.comp_aestronglyMeasurable₂ continuous_id.aestronglyMeasurable (Lp.aestronglyMeasurable w))
      (ae_of_all _ fun z => bound z (w z))
  let op := fun w : Lp ℂ 2 μ => (mem w).toLp _
  have acts (w : Lp ℂ 2 μ) : ⇑(op w) =ᵐ[μ] (fun z => planeMetricFlux A B C z (w z)) :=
    (mem w).coeFn_toLp
  let T : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ := {
    toFun := op
    map_add' := by
      intro v w
      apply Lp.ext
      filter_upwards [acts (v+w),Lp.coeFn_add v w,Lp.coeFn_add (op v) (op w),acts v,acts w]
        with z h1 h2 h3 h4 h5
      rw [h1,h2,h3]
      change planeMetricFlux A B C z (v z+w z)=op v z+op w z
      rw [h4,h5,flux_add]
    map_smul' := by
      intro r w
      apply Lp.ext
      filter_upwards [acts (r • w),Lp.coeFn_smul r w,Lp.coeFn_smul r (op w),acts w]
        with z h1 h2 h3 h4
      change op (r • w) z=(r • op w) z
      rw [h1,h2,h3]
      change planeMetricFlux A B C z (r • w z)=r • op w z
      rw [h4,flux_smul] }
  refine ⟨T.mkContinuous L (fun w => Lp.norm_le_mul_norm_of_ae_le_mul ?_),acts⟩
  filter_upwards [acts w] with z hz
  change ‖op w z‖≤L*‖w z‖
  rw [hz]
  exact bound z (w z)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_planeMetricFlux_L2
