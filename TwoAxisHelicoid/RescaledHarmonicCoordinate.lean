module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped ContDiff

theorem rescaled_scalar_pullback {A B C v : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (p : ℂ)
    {s : ℝ} (sp : 0<s) (sv : ContDiff ℝ ∞ v) (positive : 0<fderiv ℝ v 0 1)
    (harm : ∀ z∈ball (0:ℂ) 1,
      fderiv ℝ (fun y => C (p+s • y)*fderiv ℝ v y 1-B (p+s • y)*fderiv ℝ v y I) z 1 =
      fderiv ℝ (fun y => B (p+s • y)*fderiv ℝ v y 1-A (p+s • y)*fderiv ℝ v y I) z I) :
    ∃ u : ℂ → ℝ, fderiv ℝ u p 1=1 ∧ ∀ z∈ball p s, ContDiffAt ℝ ∞ u z ∧
      fderiv ℝ (fun y => C y*fderiv ℝ u y 1-B y*fderiv ℝ u y I) z 1 =
      fderiv ℝ (fun y => B y*fderiv ℝ u y 1-A y*fderiv ℝ u y I) z I := by
  let Q := fun y : ℂ => s⁻¹ • (y-p)
  let P := fun z : ℂ => p+s • z
  let k := s/(fderiv ℝ v 0 1)
  let u := k • (v ∘ Q)
  have sQ : ContDiff ℝ ∞ Q := (contDiff_id.sub contDiff_const).const_smul _
  have sP : ContDiff ℝ ∞ P := contDiff_const.add (contDiff_id.const_smul s)
  have dQ (x : ℂ) : HasFDerivAt Q (s⁻¹ • ContinuousLinearMap.id ℝ ℂ) x := by
    simpa only [Q,Pi.smul_apply] using! (hasFDerivAt_sub_const (𝕜:=ℝ) (x:=x) p).const_smul (s⁻¹)
  have diff (f : ℂ → ℝ) (sf : ContDiff ℝ ∞ f) (a : ℝ) (x d : ℂ) :
      fderiv ℝ (a • (f ∘ Q)) x d=(a*s⁻¹)*fderiv ℝ f (Q x) d := by
    rw [fderiv_const_smul_field,Pi.smul_apply,fderiv_comp x (sf.differentiable (by simp) (Q x))
      (dQ x).differentiableAt,(dQ x).fderiv]
    simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      map_smul,smul_eq_mul,mul_assoc]
  have inv (x : ℂ) : P (Q x)=x := by simp [P,Q,sp.ne']
  let flux := fun c b : ℂ → ℝ => fun y => c (P y)*fderiv ℝ v y 1-b (P y)*fderiv ℝ v y I
  have fc {c b : ℂ → ℝ} (c1 : ContDiff ℝ ∞ c) (b1 : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (flux c b) :=
    ((c1.comp sP).mul ((sv.fderiv_right (by simp)).clm_apply contDiff_const)).sub
      ((b1.comp sP).mul ((sv.fderiv_right (by simp)).clm_apply contDiff_const))
  have pull (c b : ℂ → ℝ) : (fun y => c y*fderiv ℝ u y 1-b y*fderiv ℝ u y I) =
      (k*s⁻¹) • (flux c b ∘ Q) := by
    funext y
    change c y*fderiv ℝ (k • (v ∘ Q)) y 1-b y*fderiv ℝ (k • (v ∘ Q)) y I= (k*s⁻¹)*flux c b (Q y)
    rw [diff v sv,diff v sv]
    dsimp only [flux]
    rw [inv]
    ring
  refine ⟨u,?_,?_⟩
  · change fderiv ℝ (k • (v ∘ Q)) p 1=1
    rw [diff v sv]
    simp only [Q,sub_self,smul_zero,k]
    field_simp [positive.ne',sp.ne']
  · intro x hx
    have mem : Q x∈ball (0:ℂ) 1 := by
      change dist (s⁻¹ • (x-p)) 0<1
      rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr sp).le,inv_mul_lt_iff₀ sp, mul_one]
      simpa only [dist_eq_norm] using mem_ball.mp hx
    refine ⟨((sv.comp sQ).const_smul k).contDiffAt,?_⟩
    rw [pull C B,pull B A,diff _ (fc sc sb),diff _ (fc sb sa)]
    exact congrArg (fun b : ℝ => (k*s⁻¹*s⁻¹)*b) (harm _ mem)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rescaled_scalar_pullback
