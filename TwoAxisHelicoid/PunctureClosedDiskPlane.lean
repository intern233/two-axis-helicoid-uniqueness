module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section
namespace TwoAxisHelicoid
open Complex Set Metric Topology

noncomputable def collarRadialPoint (c : ℂ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  c+(f ‖z-c‖/‖z-c‖) • (z-c)

private theorem collarRadialPoint_radius {c z : ℂ} {f : ℝ → ℝ} (distpos : 0<‖z-c‖)
    (fp : 0<f ‖z-c‖) : ‖collarRadialPoint c f z-c‖=f ‖z-c‖ := by
  simp only [collarRadialPoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  rw [abs_of_pos (div_pos fp distpos),div_mul_cancel₀ _ distpos.ne']

private theorem collarRadialPoint_comp {c z : ℂ} {f g : ℝ → ℝ} (distpos : 0<‖z-c‖)
    (fp : 0<f ‖z-c‖) (inverse : g (f ‖z-c‖)=‖z-c‖) :
    collarRadialPoint c g (collarRadialPoint c f z)=z := by
  rw [collarRadialPoint,collarRadialPoint_radius distpos fp,inverse]
  simp only [collarRadialPoint,add_sub_cancel_left,smul_smul]
  rw [show ‖z-c‖/f ‖z-c‖*(f ‖z-c‖/‖z-c‖)=1 by field_simp [distpos.ne',fp.ne'],
    one_smul,add_sub_cancel]

private theorem collarRadialPoint_continuousAt {c z : ℂ} {f : ℝ → ℝ} (cf : Continuous f)
    (non : z≠c) : ContinuousAt (collarRadialPoint c f) z := by
  have h := (continuous_id.sub continuous_const : Continuous (fun w : ℂ => w-c)).continuousAt (x:=z)
  exact continuousAt_const.add (((cf.continuousAt.comp h.norm).div h.norm (norm_ne_zero_iff.mpr (sub_ne_zero.mpr non))).smul h)

/-- Replace one puncture by a closed round disk while fixing all points
from radius twice the disk radius onwards. The outer support is the
same for the forward and inverse maps. -/
theorem puncture_and_disk_plane_homeomorphism (c : ℂ) {r : ℝ} (hr : 0<r) :
    ∃ e : {z : ℂ // z≠c} ≃ₜ {z : ℂ // r<‖z-c‖},
      (∀ z, 2*r≤‖z.1-c‖ → (e z).1=z.1) ∧
      (∀ z, ‖z.1-c‖≤2*r → ‖(e z).1-c‖≤2*r) ∧
      (∀ z, 2*r≤‖z.1-c‖ → (e.symm z).1=z.1) ∧
      (∀ z, ‖z.1-c‖≤2*r → ‖(e.symm z).1-c‖≤2*r) := by
  let f (s : ℝ) := max s (r+s/2)
  let g (s : ℝ) := min s (2*(s-r))
  have cf : Continuous f := continuous_id.max (continuous_const.add (continuous_id.div_const 2))
  have cg : Continuous g := continuous_id.min (continuous_const.mul (continuous_id.sub continuous_const))
  have fg (s : ℝ) : g (f s)=s ∧ f (g s)=s := by
    by_cases h : 2*r≤s
    · have large : r+s/2≤s := by linarith
      have pos : s≤2*(s-r) := by linarith
      simp [f,g,max_eq_left large,min_eq_left pos]
    · have small : s≤r+s/2 := by linarith
      have thin : 2*(s-r)≤s := by linarith
      have second : 2*(r+s/2-r)≤r+s/2 := by linarith
      have first : 2*(s-r)≤r+2*(s-r)/2 := by linarith
      simp only [f,g,max_eq_right small,min_eq_right thin,min_eq_right second,max_eq_right first]
      constructor <;> ring
  have positiveF {s : ℝ} (sp : 0<s) : r<f s := (lt_add_of_pos_right r (half_pos sp)).trans_le (le_max_right _ _)
  have positiveG {s : ℝ} (sp : r<s) : 0<g s := lt_min (hr.trans sp) (mul_pos (by norm_num) (sub_pos.mpr sp))
  let F (z : {w : ℂ // w≠c}) : {w : ℂ // r<‖w-c‖} :=
    let d := norm_pos_iff.mpr (sub_ne_zero.mpr z.2)
    ⟨collarRadialPoint c f z, (collarRadialPoint_radius d (hr.trans (positiveF d))) ▸ positiveF d⟩
  let G (z : {w : ℂ // r<‖w-c‖}) : {w : ℂ // w≠c} := by
    refine ⟨collarRadialPoint c g z,sub_ne_zero.mp (norm_pos_iff.mp ?_)⟩
    rw [collarRadialPoint_radius (hr.trans z.2) (positiveG z.2)]
    exact positiveG z.2
  have left (z : {w : ℂ // w≠c}) : G (F z)=z := by
    have d := norm_pos_iff.mpr (sub_ne_zero.mpr z.2)
    exact Subtype.ext (collarRadialPoint_comp d (hr.trans (positiveF d)) (fg _).1)
  have right (z : {w : ℂ // r<‖w-c‖}) : F (G z)=z :=
    Subtype.ext (collarRadialPoint_comp (hr.trans z.2) (positiveG z.2) (fg _).2)
  let e : {z : ℂ // z≠c} ≃ₜ {z : ℂ // r<‖z-c‖} :=
    { toFun:=F,invFun:=G,left_inv:=left,right_inv:=right,
      continuous_toFun:=continuous_iff_continuousAt.mpr fun z =>
        tendsto_subtype_rng.mpr ((collarRadialPoint_continuousAt cf z.2).comp continuous_subtype_val.continuousAt),
      continuous_invFun:=continuous_iff_continuousAt.mpr fun z =>
        tendsto_subtype_rng.mpr ((collarRadialPoint_continuousAt cg (sub_ne_zero.mp (norm_pos_iff.mp (hr.trans z.2)))).comp
          continuous_subtype_val.continuousAt) }
  have fixed {u : ℂ} {a : ℝ → ℝ} (non : 0<‖u-c‖) (same : a ‖u-c‖=‖u-c‖) :
      collarRadialPoint c a u=u := by
    rw [collarRadialPoint,same,div_self non.ne',one_smul,add_sub_cancel]
  refine ⟨e,fun z hz => fixed (norm_pos_iff.mpr (sub_ne_zero.mpr z.2)) (max_eq_left (by linarith)),?_,
    fun z hz => fixed (hr.trans z.2) (min_eq_left (by linarith)),?_⟩
  · intro z hz
    have d := norm_pos_iff.mpr (sub_ne_zero.mpr z.2)
    exact (collarRadialPoint_radius d (hr.trans (positiveF d))).trans_le (max_le hz (by linarith))
  · intro z hz
    exact (collarRadialPoint_radius (hr.trans z.2) (positiveG z.2)).trans_le ((min_le_left _ _).trans hz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncture_and_disk_plane_homeomorphism
