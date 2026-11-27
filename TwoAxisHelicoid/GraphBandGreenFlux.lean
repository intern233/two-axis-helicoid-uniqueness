import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Set MeasureTheory
open scoped Interval ContDiff

/-- The vertical shear puts an actual smooth boundary graph on the
bottom of a coordinate rectangle. The second coordinate is vertical
distance in the chart, so its area Jacobian is one. -/
noncomputable def realGraphShear (φ : ℝ → ℝ) (q : ℝ×ℝ) : ℝ×ℝ := (q.1,q.2+φ q.1)

private noncomputable def realGraphHomeo (φ : ℝ → ℝ) (c : Continuous φ) : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) where
  toFun := realGraphShear φ
  invFun := fun p => (p.1,p.2-φ p.1)
  left_inv := fun _ => Prod.ext rfl (add_sub_cancel_right _ _)
  right_inv := fun _ => Prod.ext rfl (sub_add_cancel _ _)
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (c.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (c.comp continuous_fst))

theorem real_graph_shear_preserves_area {φ : ℝ → ℝ} (c : Continuous φ) :
    MeasurePreserving (realGraphShear φ) volume volume := by
  exact MeasurePreserving.skew_product (g:=fun x y : ℝ => y+φ x) (MeasurePreserving.id volume)
    (measurable_snd.add (c.measurable.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (φ x))

private theorem graph_shear_differential_columns {φ : ℝ → ℝ} {x : ℝ×ℝ}
    (p : DifferentiableAt ℝ φ x.1) :
    fderiv ℝ (realGraphShear φ) x (1,0)=(1,deriv φ x.1) ∧ fderiv ℝ (realGraphShear φ) x (0,1)=(0,1) := by
  let D := (p.hasDerivAt.hasFDerivAt.comp x hasFDerivAt_fst)
  have A := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add D)
  rw [show fderiv ℝ (realGraphShear φ) x=_ from A.fderiv]
  constructor <;> apply Prod.ext <;> simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- Divergence on a curvilinear rectangle bounded by two vertical
translates of a smooth graph. Each normal flux includes its physical
line element; the two graph sides use Q-φ'P. -/
theorem divergence_on_graph_band {φ : ℝ → ℝ} (cφ : ContDiff ℝ 2 φ) (a b : ℝ×ℝ)
    (order : a≤b) {P Q : ℝ×ℝ → ℝ}
    (cP : ∀ z∈realGraphShear φ '' Icc a b, ContDiffAt ℝ 1 P z)
    (cQ : ∀ z∈realGraphShear φ '' Icc a b, ContDiffAt ℝ 1 Q z) :
    let T := realGraphShear φ
    let N := fun q : ℝ×ℝ => Q (T q)-deriv φ q.1*P (T q)
    (∫ z in T '' Icc a b, fderiv ℝ P z (1,0)+fderiv ℝ Q z (0,1))=
      (((∫ x in a.1..b.1, N (x,b.2))-(∫ x in a.1..b.1, N (x,a.2)))+
       (∫ y in a.2..b.2, P (T (b.1,y))))-(∫ y in a.2..b.2, P (T (a.1,y))) := by
  let T := realGraphShear φ
  let N := fun q : ℝ×ℝ => Q (T q)-deriv φ q.1*P (T q)
  let X := P ∘ T
  have sT : ContDiff ℝ 1 T :=
    contDiff_fst.prodMk (contDiff_snd.add ((cφ.of_le (by norm_num)).comp contDiff_fst))
  have slope : ContDiff ℝ 1 (deriv φ) := cφ.deriv'
  have sX (z : ℝ×ℝ) (hz : z∈Icc a b) : ContDiffAt ℝ 1 X z :=
    (cP _ ⟨z,hz,rfl⟩).comp z sT.contDiffAt
  have sN (z : ℝ×ℝ) (hz : z∈Icc a b) : ContDiffAt ℝ 1 N z :=
    ((cQ _ ⟨z,hz,rfl⟩).comp z sT.contDiffAt).sub ((slope.comp contDiff_fst).contDiffAt.mul (sX _ hz))
  have columns (z : ℝ×ℝ) (hz : z∈Icc a b) :
      fderiv ℝ X z (1,0)+fderiv ℝ N z (0,1)=fderiv ℝ P (T z) (1,0)+fderiv ℝ Q (T z) (0,1) := by
    have dz := (sT.differentiable one_ne_zero z).hasFDerivAt
    have du := ((cP _ ⟨z,hz,rfl⟩).differentiableAt one_ne_zero).hasFDerivAt.comp z dz
    have dv := ((cQ _ ⟨z,hz,rfl⟩).differentiableAt one_ne_zero).hasFDerivAt.comp z dz
    have ds := (slope.differentiable one_ne_zero z.1).hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst
    have dn := dv.sub (ds.mul du)
    obtain ⟨c1,c2⟩ := graph_shear_differential_columns (x:=z) (cφ.differentiable (by norm_num) z.1)
    change fderiv ℝ T z (1,0)=(1,deriv φ z.1) at c1
    change fderiv ℝ T z (0,1)=(0,1) at c2
    rw [show fderiv ℝ X z=_ from du.fderiv,show fderiv ℝ N z=_ from dn.fderiv]
    simp only [sub_apply,add_apply,smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      show (ContinuousLinearMap.fst ℝ ℝ ℝ) (0,1)=0 from rfl,Function.comp_apply,
      smul_eq_mul,zero_mul,mul_zero,add_zero,c1,c2]
    rw [show ((1:ℝ),deriv φ z.1)=(1,0)+deriv φ z.1 • (0,1) by ext <;> simp,map_add,map_smul]
    simp only [smul_eq_mul]
    ring
  have integrable : IntegrableOn (fun z => fderiv ℝ X z (1,0)+fderiv ℝ N z (0,1)) (Icc a b) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro z hz
    exact (((sX z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const |>.add
      (((sN z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)).continuousWithinAt
  have sub : Ioo a.1 b.1 ×ˢ Ioo a.2 b.2⊆Icc a b := fun _ hz =>
    ⟨⟨hz.1.1.le,hz.2.1.le⟩,⟨hz.1.2.le,hz.2.2.le⟩⟩
  have flux := integral_divergence_prod_Icc_of_hasFDerivAt_of_le X N (fderiv ℝ X) (fderiv ℝ N) a b order
    (fun z hz => (sX z hz).continuousAt.continuousWithinAt)
    (fun z hz => (sN z hz).continuousAt.continuousWithinAt)
    (fun z hz => ((sX z (sub hz)).differentiableAt one_ne_zero).hasFDerivAt)
    (fun z hz => ((sN z (sub hz)).differentiableAt one_ne_zero).hasFDerivAt) integrable
  have mapped := (real_graph_shear_preserves_area cφ.continuous).setIntegral_image_emb
    (realGraphHomeo φ cφ.continuous).measurableEmbedding (fun z => fderiv ℝ P z (1,0)+fderiv ℝ Q z (0,1)) (Icc a b)
  exact mapped.trans ((setIntegral_congr_fun measurableSet_Icc (fun z hz => (columns z hz).symm)).trans flux)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.real_graph_shear_preserves_area
#print axioms TwoAxisHelicoid.divergence_on_graph_band
