import TwoAxisHelicoid.KernelEllipticHeat

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] thetaA thetaW

theorem thetaW_hasDerivAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (thetaW t) (-((rhombicPeriodPair t ht).weierstrassP z+thetaEtaExpression t)) z := by
  have hd := (thetaZeta_hasDerivAt_of_pos ht ht hz).sub
    ((hasDerivAt_id z).const_mul (thetaEtaExpression t))
  convert hd using 1
  · funext w
    simp only [thetaW,Pi.sub_apply,id_eq]
  · simp only [mul_one]
    ring

theorem thetaW_add_two (t : ℝ) (z : ℂ) : thetaW t (z+2) = thetaW t z := by
  unfold thetaW
  rw [thetaZeta_add_two]
  ring

theorem weighted_spatial_integral {t a : ℝ} (ht : 0 < t) (_ha : a ∈ Ioo (0:ℝ) 2) :
    (∫ x : ℝ in (-1)..1, thetaW t ((x:ℂ)+I*((t/2:ℝ):ℂ))*
      deriv (thetaA t a) ((x:ℂ)+I*((t/2:ℝ):ℂ))) =
    ∫ x : ℝ in (-1)..1, ((rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))+
      thetaEtaExpression t)*thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)) := by
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  let A := fun x : ℝ => thetaA t a (z x)
  let P := fun x : ℝ => (rhombicPeriodPair t ht).weierstrassP (z x)
  let W := fun x : ℝ => thetaW t (z x)
  let D := fun x : ℝ => deriv (thetaA t a) (z x)
  have harg (x : ℝ) : HasDerivAt z 1 x := by
    simpa only [id_eq,Complex.ofReal_one] using (hasDerivAt_id x).ofReal_comp.add_const (I*((t/2:ℝ):ℂ))
  have hW (x : ℝ) : HasDerivAt W (-(P x+thetaEtaExpression t)) x := by
    simpa only [Function.comp_def,mul_one] using (thetaW_hasDerivAt ht (rhombic_midline_not_mem ht x)).comp x (harg x)
  have hA (x : ℝ) : HasDerivAt A (D x) x := thetaA_horizontal_hasDerivAt ht a (t/2) x (horizontal_midline_regular ht x)
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hWc : Continuous W := continuous_iff_continuousAt.mpr (fun x => (hW x).continuousAt)
  have hPc : Continuous P := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := z) (x := x) (harg x).continuousAt
  have hDc : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((thetaA_deriv_continuousOn ht a).continuousAt
      ((thetaRegular_isOpen ht).mem_nhds (horizontal_midline_regular ht x))).comp
        (f := z) (x := x) (harg x).continuousAt
  have hprod (x : ℝ) : HasDerivAt (fun y : ℝ => W y*A y)
      (W x*D x-(P x+thetaEtaExpression t)*A x) x := by
    convert (hW x).mul (hA x) using 1
    ring
  have h1 : IntervalIntegrable (fun x : ℝ => W x*D x) volume (-1) 1 :=
    (hWc.mul hDc).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable (fun x : ℝ => (P x+thetaEtaExpression t)*A x) volume (-1) 1 :=
    ((hPc.add continuous_const).mul hAc).intervalIntegrable (-1) 1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_hx : x ∈ uIcc (-1:ℝ) 1) => hprod x) (h1.sub h2)
  have hpA : A 1 = A (-1) := by
    have hh := thetaA_periodic t a (z (-1))
    have he : z (-1)+2 = z 1 := by dsimp [z]; push_cast; ring
    rw [he] at hh
    exact hh
  have hpW : W 1 = W (-1) := by
    have hh := thetaW_add_two t (z (-1))
    have he : z (-1)+2 = z 1 := by dsimp [z]; push_cast; ring
    rw [he] at hh
    exact hh
  rw [intervalIntegral.integral_sub h1 h2,hpA,hpW,sub_self] at hh
  exact sub_eq_zero.mp hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weighted_spatial_integral
