import TwoAxisHelicoid.CentralConjugateHeightInterval
import TwoAxisHelicoid.AxisTotalPhase

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- In the normalization of the manuscript, the two conjugate saddle
heights are explicit in the axis constant and the lattice height. -/
theorem conjugate_saddle_heights_formula {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (closed : thetaG t a=0) :
    let H := actualComplexHeight t a 1 ht
    let C := axisConstant t ht a
    (H a).im=C-Real.pi/t ∧ (H (((1-a:ℝ):ℂ)+I*t)).im= -C := by
  intro H C
  let L := rhombicPeriodPair t ht
  have realW := rhombic_weierstrassP_real ht a
  have close := closed_height_weierstrass_value ht ha closed
  have eq : (thetaEtaExpression t).re+(L.weierstrassP a).re=Real.pi/t := by
    change _+((rhombicPeriodPair t ht).weierstrassP a).re=_
    rw [close,sub_re,← ofReal_div,ofReal_re]
    ring
  have off := real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))
  have q := thetaZeta_add_half_of_pos ht ht (show -(a:ℂ)∉L.lattice by simpa using off)
  rw [thetaZeta_neg] at q
  constructor
  · dsimp only [H,actualComplexHeight,C,axisConstant]
    simp only [ofReal_one,mul_one,Complex.mul_im,neg_im,neg_re,I_re,I_im,neg_zero,zero_mul,
      neg_one_mul,zero_add,Complex.add_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    change (thetaEtaExpression t).re+(L.weierstrassP a).re=Real.pi/t at eq
    dsimp only [L] at eq
    linarith
  · have arg : ((1-a:ℝ):ℂ)+I*t= -(a:ℂ)+(1+I*t) := by push_cast; ring
    dsimp only [H,actualComplexHeight,C,axisConstant]
    rw [arg,q]
    simp [Complex.mul_im,Complex.mul_re,rhombic_weierstrassP_real ht a,thetaEtaExpression_real]
    ring

/-- For any closed TwoAxisHelicoid immersion, the center arc runs strictly inside
the negative conjugate-height interval (C−π/t,−C). In particular
0 < C < π/(2t) follows from the geometry of the height function. -/
theorem closed_central_saddle_interval {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (closed : thetaG t a=0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let C := axisConstant t ht a
    let H := actualComplexHeight t a 1 ht
    0<C ∧ C<Real.pi/(2*t) ∧
      ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2) ∧
        (fun y : ℝ => (H ((r y:ℂ)+I*y)).im) '' Ioo 0 t=Ioo (C-Real.pi/t) (-C) := by
  intro C H
  obtain ⟨r,sp,_,_,_,_,order,img⟩ := actual_central_conjugate_height_interval ht ha d per
  obtain ⟨lo,hi⟩ := conjugate_saddle_heights_formula ht ha closed
  rw [lo,hi] at order img
  have b : C<(Real.pi/t)/2 := by dsimp only [C]; linarith
  exact ⟨axisConstant_pos ht ha,(by rwa [div_div, mul_comm t (2:ℝ)] at b),r,sp,img⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_central_saddle_interval
