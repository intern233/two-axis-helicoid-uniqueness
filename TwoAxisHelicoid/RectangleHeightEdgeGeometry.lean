import TwoAxisHelicoid.RectangleEdgeShapeSound
import TwoAxisHelicoid.CentralBandLevelGraphs
import Mathlib.Analysis.Convex.Deriv

namespace TwoAxisHelicoid
open Complex Set

/-- The level interval is bounded on its left by a convex height edge
and on its right by a strictly increasing height edge. -/
theorem rectangle_height_edge_shapes
    (left : CheckedRectangleShape true (1/8) (3/8)) (right : CheckedRectangleShape false (1/8) (3/8)) :
    let p := certifiedClosedParameters
    let F := fun x y : ℝ => (actualComplexHeight p.t p.a 1 p.height_pos ((x:ℂ)+I*y)).re
    let J := Icc (1/8:ℝ) (3/8)
    ConvexOn ℝ J (F (1/2)) ∧ StrictMonoOn (F (5/8)) J := by
  intro p F J
  let P := certifiedPeriodPair
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  let V := fun x y => (P.weierstrassP p.a-P.weierstrassP (Z x y)).re
  have ht : (3/8:ℝ)<p.t := (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have off (x y : ℝ) (hy : y∈J) : Z x y∉P.lattice := rhombic_horizontal_strip_not_mem p.height_pos (by
    change (Z x y).im∈Ioo 0 p.t
    simpa only [Z,add_im,ofReal_im,I_mul_im,ofReal_re,zero_add] using (show y∈Ioo 0 p.t from ⟨by linarith [hy.1],hy.2.trans_lt ht⟩))
  have dz (x y : ℝ) : HasDerivAt (Z x) I y := by
    simpa [Z] using ((hasDerivAt_id y).ofReal_comp.const_mul I).const_add (x:ℂ)
  have first (x y : ℝ) (hy : y∈J) : HasDerivAt (F x) (V x y) y := by
    have h := reCLM.hasFDerivAt.comp_hasDerivAt y ((actualComplexHeight_hasDerivAt (a:=p.a) (c:=1) p.height_pos (off x y hy)).scomp y (dz x y))
    change HasDerivAt (F x) (I*(I*(1:ℂ)*(P.weierstrassP (Z x y)-P.weierstrassP p.a))).re y at h
    simpa only [mul_one,← mul_assoc,I_mul_I,neg_one_mul,neg_sub,V] using h
  have second (x y : ℝ) (hy : y∈J) : HasDerivAt (V x) (P.derivWeierstrassP (Z x y)).im y := by
    have h := reCLM.hasFDerivAt.comp_hasDerivAt y
      (HasDerivAt.const_sub (P.weierstrassP p.a) ((rhombic_weierstrassP_hasDerivAt p.height_pos (off x y hy)).scomp y (dz x y)))
    change HasDerivAt (V x) (-(I*P.derivWeierstrassP (Z x y))).re y at h
    simpa only [neg_re,I_mul_re,neg_neg] using h
  have bounds {y : ℝ} (hy : y∈J) : y∈Icc ((1/8:ℚ):ℝ) ((3/8:ℚ):ℝ) := by norm_num; exact hy
  have cu (y : ℝ) (hy : y∈J) : 0<(P.derivWeierstrassP (Z (1/2) y)).im := by
    have e := left.sound y (bounds hy)
    change 0<(thetaLogThird p.t (Z (1/2) y)).im at e
    rwa [thetaLogThird_eq_weierstrassP_deriv p.height_pos (off _ y hy)] at e
  have slope (y : ℝ) (hy : y∈J) : 0<V (5/8) y := by
    have v := right.sound y (bounds hy)
    change 0<Real.pi/p.t-(thetaLogSecond p.t (Z (5/8) y)).re at v
    have a := thetaG_eq_weierstrassP_of_pos p.height_pos p.height_pos p.a
      (real_not_mem_rhombic_lattice_of_pos p.height_pos p.abscissa_mem.1 (show p.a<2 by linarith [p.abscissa_mem.2]))
    rw [p.vertical_closed] at a
    have b := thetaLogSecond_eq_weierstrassP_add_eta_of_pos p.height_pos p.height_pos (off (5/8) y hy)
    have eq : ((Real.pi/p.t:ℝ):ℂ)-thetaLogSecond p.t (Z (5/8) y)=P.weierstrassP p.a-P.weierstrassP (Z (5/8) y) := by
      change _=(rhombicPeriodPair p.t p.height_pos).weierstrassP p.a-(rhombicPeriodPair p.t p.height_pos).weierstrassP (Z (5/8) y)
      linear_combination a-b
    change 0<(P.weierstrassP p.a-P.weierstrassP (Z (5/8) y)).re
    rwa [← eq,sub_re,ofReal_re]
  refine ⟨convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (fun y hy => (first _ y hy).continuousAt.continuousWithinAt)
    (fun y hy => (first _ y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => (second _ y (interior_subset hy)).hasDerivWithinAt) (fun y hy => (cu y (interior_subset hy)).le),?_⟩
  exact strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun y hy => (first _ y hy).continuousAt.continuousWithinAt)
    (fun y hy => (first _ y (interior_subset hy)).deriv.symm ▸ slope y (interior_subset hy))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_height_edge_shapes
