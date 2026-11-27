import TwoAxisHelicoid.RegularGraphCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

/-- Orthogonal projection in the parameter plane onto a vertical
line. -/
def verticalParameterFoot (a : ℝ) (w : ℂ) : ℂ := ⟨a,w.im⟩

theorem continuous_verticalParameterFoot (a : ℝ) : Continuous (verticalParameterFoot a) :=
  equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_im)

private theorem sub_verticalParameterFoot (a : ℝ) (w : ℂ) :
    w-verticalParameterFoot a w=(w.re-a) • (1:ℂ) := by
  apply Complex.ext <;> simp [verticalParameterFoot,Complex.real_smul]

/-- The transverse divided difference filled by its actual derivative
at points on the vertical line. Both base coordinates vary. -/
noncomputable def verticalTransverseDifference (P : ℂ → ℂ) (a : ℝ) (w : ℂ) : ℂ :=
  if w.re=a then fderiv ℝ P w 1 else (P w-P (verticalParameterFoot a w))/((w.re-a:ℝ):ℂ)

theorem verticalTransverseDifference_on {a : ℝ} {w : ℂ} (P : ℂ → ℂ) (hw : w.re=a) :
    verticalTransverseDifference P a w=fderiv ℝ P w 1 := by simp [verticalTransverseDifference,hw]

theorem verticalTransverseDifference_factor (P : ℂ → ℂ) (a : ℝ) (w : ℂ) :
    P w-P (verticalParameterFoot a w)=((w.re-a:ℝ):ℂ)*verticalTransverseDifference P a w := by
  by_cases he : w.re=a
  · have eq : verticalParameterFoot a w=w := Complex.ext he.symm rfl
    simp [eq,he]
  · simp only [verticalTransverseDifference,ite_eq_right he]
    exact (mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr he))).symm

/-- Strict real differentiability controls two points tending to the
same point independently. It gives continuity of the transverse
quotient even for approaches tangent to the parameter axis. -/
theorem verticalTransverseDifference_continuousAt {P : ℂ → ℂ} {a : ℝ} {z : ℂ}
    (hp : AnalyticAt ℝ P z) (hz : z.re=a) : ContinuousAt (verticalTransverseDifference P a) z := by
  let L := fderiv ℝ P z
  let foot := verticalParameterFoot a
  have ff : foot z=z := Complex.ext hz.symm rfl
  have pair : Tendsto (fun w => (w,foot w)) (𝓝 z) (𝓝 (z,z)) := by
    have hh : Tendsto (fun w => (w,foot w)) (𝓝 z) (𝓝 (z,foot z)) := (continuous_id.prodMk (continuous_verticalParameterFoot a)).continuousAt.tendsto
    rwa [ff] at hh
  have d : HasStrictFDerivAt P L z := (hp.contDiffAt (n := 1)).hasStrictFDerivAt one_ne_zero
  have cd : ContinuousAt (fun w => fderiv ℝ P w 1) z :=
    (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).continuous.continuousAt.comp hp.fderiv.continuousAt
  unfold ContinuousAt
  rw [verticalTransverseDifference_on P hz]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ex := pair.eventually (d.isLittleO.bound (half_pos hε))
  have ed := (Metric.tendsto_nhds.mp cd.tendsto) ε hε
  filter_upwards [ex,ed] with w estimate same
  by_cases hw : w.re=a
  · rw [verticalTransverseDifference_on P hw]
    exact same
  let δ := w.re-a
  have nz : δ ≠ 0 := sub_ne_zero.mpr hw
  have nc : (δ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nz
  have sub : w-foot w=δ • (1:ℂ) := sub_verticalParameterFoot a w
  change ‖P w-P (foot w)-L (w-foot w)‖ ≤ ε/2 * ‖w-foot w‖ at estimate
  rw [sub,map_smul,norm_smul,Real.norm_eq_abs,norm_one,mul_one,Complex.real_smul] at estimate
  have eq : verticalTransverseDifference P a w - L 1 = (P w-P (foot w)-(δ:ℂ)*L 1)/(δ:ℂ) := by
    simp only [verticalTransverseDifference,ite_eq_right hw]
    change (P w-P (foot w))/(δ:ℂ)-L 1=_
    field_simp
  rw [dist_eq_norm,eq,norm_div,Complex.norm_real,Real.norm_eq_abs]
  apply (div_lt_iff₀ (abs_pos.mpr nz)).mpr
  exact estimate.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hε) (abs_pos.mpr nz))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.verticalTransverseDifference_continuousAt
