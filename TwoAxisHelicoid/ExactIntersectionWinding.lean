import TwoAxisHelicoid.AxisHelicoidSideDerivative
import TwoAxisHelicoid.AxisRectangleSigns
import TwoAxisHelicoid.AxisSideWindingBound
import TwoAxisHelicoid.PunctureFilledMap

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaGauss

/-- The exact axis-only intersection with the calibrated helicoid forces
the basic two winding indices on the actual embedded punctured torus.
This argument only uses the sign on the two open parameter rectangles
and their inward derivatives along the vertical axis. -/
theorem harmonic_integer_axis_parameter_of_exact_intersection {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) (punctureFilledMap (rhombicPeriodPair t ht) X)
        (punctureFilledMap_periodic hX.periodic) q.1))
    (hinter : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      X z ∈ range (axisRuledHelicoid (thetaGauss t a m (I*t)) (2*(a-m)/c) (X (I*t) 2)) →
      (X z 1 = 0 ∧ X z 2 = 0) ∨ (X z 0 = 0 ∧ X z 1 = 0)) :
    m = 0 ∨ m = 1 := by
  let L := rhombicPeriodPair t ht
  let g := thetaGauss t a m (I*t)
  let α : ℝ := 2*(a-m)/c
  let b := X (I*t) 2
  let Z := fun p : ℝ × ℝ => (p.1 : ℂ)+I*p.2
  let F := fun p : ℝ × ℝ => -axisHelicoidSide g α b (X (Z p))/c
  let k := fun y : ℝ => -(L.weierstrassP (I*y)-L.weierstrassP a).re
  let δ := integerAxisPhase t a m
  have hunit : normSq g = 1 := thetaGauss_axis_normSq ht ha m ⟨ht,by linarith⟩
  let lift := fun q : PuncturedPeriodTorus L => periodTorusLift L (punctureFilledMap L X)
    (punctureFilledMap_periodic hX.periodic) q.1
  let hproj (z : ℂ) (hz : z ∉ L.lattice) : PuncturedPeriodTorus L :=
    ⟨periodTorusProjection L z,fun h => hz ((periodTorusProjection_eq_zero L z).mp h)⟩
  have hinj (z : ℂ) (hz : z ∉ L.lattice) (w : ℂ) (hw : w ∉ L.lattice) (he : X z = X w) :
      periodTorusProjection L z = periodTorusProjection L w := by
    have heq : lift (hproj z hz) = lift (hproj w hw) :=
      (punctureFilledMap_eq hz).trans (he.trans (punctureFilledMap_eq hw).symm)
    exact congrArg Subtype.val (hXi heq)
  have hhalf {l u : ℝ} (hyall : Ioo l u ⊆ Ioo 0 (2*t)) (hnt : ∀ y ∈ Ioo l u, y ≠ t) :
      (∀ y ∈ Ioo l u, 0 ≤ Real.sin (δ y)) ∨ (∀ y ∈ Ioo l u, Real.sin (δ y) ≤ 0) := by
    let R := Ioo (0 : ℝ) 1 ×ˢ Ioo l u
    have hreg {p : ℝ × ℝ} (hp : p ∈ R) : Z p ∉ L.lattice :=
      rhombic_vertical_strip_not_mem ht ⟨by linarith [hp.1.1],hp.1.2⟩ (hyall hp.2)
    have hF : ContinuousOn F R := by
      intro p hp
      have hxc : ContinuousAt (fun q => X (Z q)) p :=
        (hX.differentiable _ (hreg hp)).continuousAt.comp (by dsimp [Z]; fun_prop)
      have hside : Continuous (axisHelicoidSide g α b) := by unfold axisHelicoidSide; fun_prop
      exact ((hside.continuousAt.comp hxc).neg.div_const c).continuousWithinAt
    have hn (p : ℝ × ℝ) (hp : p ∈ R) : F p ≠ 0 := by
      intro he
      have hB : axisHelicoidSide g α b (X (Z p)) = 0 :=
        neg_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right hc)
      exact (harmonic_embedded_rectangle_avoids_axes ht hp.1 (hyall hp.2) (hnt _ hp.2) hX hinj)
        (hinter _ (hreg hp) ((axisHelicoidSide_eq_zero_iff hunit α b _).mp hB))
    have h0 (y : ℝ) (hy : y ∈ Ioo l u) : F (0,y) = 0 := by
      have hx := hX.vertical_axis_zero (integerAxis_regular_points ht ha (hyall hy)).1
        (by simp [Complex.mul_re])
      simp [F,Z,axisHelicoidSide,hx.1,hx.2]
    have hd (y : ℝ) (hy : y ∈ Ioo l u) : HasDerivAt (fun x => F (x,y)) (k y * Real.sin (δ y)) 0 := by
      have hd := (harmonic_integer_axis_side_derivative ht ha hc hG m hX hh hg (hyall hy)).neg.div_const c
      convert hd using 1
      change -(L.weierstrassP (I*y)-L.weierstrassP a).re * Real.sin (δ y) =
        -((I*(c : ℂ)*(L.weierstrassP (I*y)-L.weierstrassP a)).im * Real.sin (δ y))/c
      simp only [Complex.mul_im,Complex.I_re,zero_mul,Complex.ofReal_im,Complex.I_im,Complex.ofReal_re,
        one_mul,zero_add,Complex.mul_re,mul_zero,sub_zero]
      field_simp
    have hk (y : ℝ) (hy : y ∈ Ioo l u) : 0 < k y :=
      neg_pos.mpr (axisRegularCoefficient_den_re_neg ht ha (hyall hy))
    rcases rectangle_boundary_derivatives_one_sign hF hn h0 hd with h | h
    · exact Or.inl fun y hy => (mul_nonneg_iff_of_pos_left (hk y hy)).mp (h y hy)
    · exact Or.inr fun y hy => nonpos_of_mul_nonpos_right (h y hy) (hk y hy)
  apply integerAxisPhase_parameter_of_half_axis_signs ht ha m
  · exact hhalf (fun y hy => ⟨hy.1,by linarith [hy.2]⟩) (fun _ hy => hy.2.ne)
  · exact hhalf (fun y hy => ⟨ht.trans hy.1,hy.2⟩) (fun _ hy => hy.1.ne')

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_axis_parameter_of_exact_intersection
