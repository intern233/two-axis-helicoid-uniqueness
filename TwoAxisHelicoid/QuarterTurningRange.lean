import TwoAxisHelicoid.QuarterWeierstrassRange
import TwoAxisHelicoid.HorizontalFiberTurningCircle

namespace TwoAxisHelicoid
open Complex Set

/-- The signed angular velocity of the horizontal tangent in imaginary
height coordinates takes every real value somewhere in the open
rectangle. This statement makes no assertion about its range on an
individual horizontal level. -/
theorem horizontal_tangent_turning_range_quarter {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) :
    let U := complexOpenRect 0 1 0 t
    let L := rhombicPeriodPair t ht
    let B := fun z => (L.weierstrassP z-L.weierstrassP a)⁻¹
    let G := thetaGauss t a 1
    let turn := fun z => (deriv G z/G z/coordinateData t a 1 ht z 2).re
    B '' U={v | 0<v.im} ∧ turn '' U=univ := by
  intro U L B G turn
  have cover : B '' U={v | 0<v.im} := by
    apply Subset.antisymm
    · rintro v ⟨z,hz,rfl⟩
      exact (horizontal_gauss_turning_formula ht ha hz).1
    · intro v hv
      change 0<v.im at hv
      have nz : v≠0 := fun e => hv.ne (by rw [e]; rfl)
      have neg : (L.weierstrassP a+v⁻¹).im<0 := by
        rw [add_im,rhombic_weierstrassP_real ht,zero_add,inv_im]
        exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hv) (normSq_pos.mpr nz)
      have hit : L.weierstrassP a+v⁻¹∈L.weierstrassP '' U := by
        rw [(rhombic_quarter_weierstrass_image_and_fibers ht).1]
        exact neg
      obtain ⟨z,hz,eq⟩ := hit
      refine ⟨z,hz,?_⟩
      change (L.weierstrassP z-L.weierstrassP a)⁻¹=v
      rw [eq,add_sub_cancel_left,inv_inv]
  refine ⟨cover,eq_univ_of_forall fun h => ?_⟩
  let C := axisConstant t ht a
  let D := (L.derivWeierstrassP a).re
  have dn : D≠0 := (rhombic_weierstrassP_derivative_real_neg_of_pos ht ht ha.1 ha.2).ne
  let v : ℂ := ⟨(h/2-C)/D,1⟩
  have vin : v∈B '' U := by
    rw [cover]
    change (0:ℝ)<1
    norm_num
  obtain ⟨z,hz,ev⟩ := vin
  refine ⟨z,hz,?_⟩
  have eq := (horizontal_gauss_turning_formula ht ha hz).2.2.2
  change turn z=2*(B z).im*(C+D*(B z).re) at eq
  rw [eq,ev]
  change 2*1*(C+D*((h/2-C)/D))=h
  field_simp [dn]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_tangent_turning_range_quarter
