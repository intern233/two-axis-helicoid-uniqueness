import TwoAxisHelicoid.RhombicAxisRectangles
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Order.Interval.Set.IsoIoo

namespace TwoAxisHelicoid
open Set Complex Topology Metric

private noncomputable def intervalRescale (a b : ℝ) (h : a<b) : Ioo (-1:ℝ) 1 ≃ₜ Ioo a b where
  toFun u := ⟨a+(b-a)*(u.1+1)/2,by
    have plus : 0<(u:ℝ)+1 := by linarith [u.2.1]
    have short : (u:ℝ)+1<2 := by linarith [u.2.2]
    constructor <;> nlinarith [mul_pos (sub_pos.mpr h) plus,mul_lt_mul_of_pos_left short (sub_pos.mpr h)]⟩
  invFun u := ⟨2*(u.1-a)/(b-a)-1,by
    have pos := div_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr u.2.1)) (sub_pos.mpr h)
    have short : 2*((u:ℝ)-a)/(b-a)<2 := (div_lt_iff₀ (sub_pos.mpr h)).mpr (by linarith [u.2.2])
    constructor <;> linarith⟩
  left_inv x := by apply Subtype.ext; dsimp; field_simp; ring
  right_inv y := by apply Subtype.ext; dsimp; field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def rectangleCoordinates (a t : ℝ) :
    rhombicAxisRectangle a t ≃ₜ Ioo a (a+1) × Ioo 0 t where
  toFun z := (⟨z.1.re,z.2.1⟩,⟨z.1.im,z.2.2⟩)
  invFun p := ⟨⟨p.1.1,p.2.1⟩,p.1.2,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact equivRealProdCLM.symm.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- Both open parameter rectangles are topological disks in the usual
sense of homeomorphism to the open complex unit disk. -/
noncomputable def rhombicRectangleOpenDisk (a : ℝ) {t : ℝ} (ht : 0<t) :
    rhombicAxisRectangle a t ≃ₜ ball (0:ℂ) 1 :=
  let canonical := (orderIsoIooNegOneOne ℝ).toHomeomorph
  let x := (canonical.trans (intervalRescale a (a+1) (by linarith))).symm
  let y := (canonical.trans (intervalRescale 0 t ht)).symm
  (((rectangleCoordinates a t).trans (x.prodCongr y)).trans equivRealProdCLM.symm.toHomeomorph).trans Homeomorph.unitBall

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombicRectangleOpenDisk
