import TwoAxisHelicoid.ZeroBranchBottomDerivative
import TwoAxisHelicoid.OrientedAxisRectangle
import TwoAxisHelicoid.HoffmanWhiteWindingReduction

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaGauss

/-- The horizontal Gauss zero fixes the sign on one side of the comparison
helicoid. The reflected side has the opposite sign. Their vertical boundary
derivatives are incompatible with the negative total index of branch zero. -/
theorem harmonic_zero_branch_excluded_by_axis_intersection {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a 0 z)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hinter : range (harmonicTorusImmersion hX) ∩ range (axisRuledHelicoid I (2*a/c) 0) =
      {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)}) : False := by
  let L := rhombicPeriodPair t ht
  let α : ℝ := 2*a/c
  let Z := fun p : ℝ × ℝ => (p.1:ℂ)+I*p.2
  let F := fun p : ℝ × ℝ => -axisHelicoidSide I α 0 (X (Z p))/c
  let k := fun y : ℝ => -(L.weierstrassP (I*y)-L.weierstrassP a).re
  let δ := integerAxisPhase t a 0
  let R := Ioo (0 : ℝ) 1 ×ˢ Ioo 0 t
  have hreg {p : ℝ × ℝ} (hp : p ∈ R) : Z p ∉ L.lattice :=
    rhombic_vertical_strip_not_mem ht ⟨by linarith [hp.1.1],hp.1.2⟩ ⟨hp.2.1,by linarith [hp.2.2]⟩
  have hF : ContinuousOn F R := by
    intro p hp
    have hx := (hX.differentiable _ (hreg hp)).continuousAt.comp
      (f := Z) (by dsimp [Z]; fun_prop : ContinuousAt Z p)
    have hs : Continuous (axisHelicoidSide I α 0) := by unfold axisHelicoidSide; fun_prop
    exact ((hs.continuousAt.comp hx).neg.div_const c).continuousWithinAt
  have hinj (z : ℂ) (hr : z ∉ L.lattice) (w : ℂ) (hs : w ∉ L.lattice) (he : X z = X w) :
      periodTorusProjection L z = periodTorusProjection L w := by
    let q : PuncturedPeriodTorus L := ⟨periodTorusProjection L z,fun h => hr ((periodTorusProjection_eq_zero L z).mp h)⟩
    let r : PuncturedPeriodTorus L := ⟨periodTorusProjection L w,fun h => hs ((periodTorusProjection_eq_zero L w).mp h)⟩
    have hh : harmonicTorusImmersion hX q = harmonicTorusImmersion hX r :=
      (harmonicTorusImmersion_projection hX hr).trans (he.trans (harmonicTorusImmersion_projection hX hs).symm)
    exact congrArg Subtype.val (hXi hh)
  have hn (p : ℝ × ℝ) (hp : p ∈ R) : F p ≠ 0 := by
    intro he
    have hs : axisHelicoidSide I α 0 (X (Z p)) = 0 :=
      neg_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right hc)
    have hm : X (Z p) ∈ range (harmonicTorusImmersion hX) ∩ range (axisRuledHelicoid I α 0) := by
      refine ⟨?_,(axisHelicoidSide_eq_zero_iff (by simp : normSq I = 1) α 0 _).mp hs⟩
      rw [harmonicTorusImmersion_range hX]
      exact ⟨_,hreg hp,rfl⟩
    rw [hinter] at hm
    exact (harmonic_embedded_rectangle_avoids_axes ht hp.1 ⟨hp.2.1,by linarith [hp.2.2]⟩
      hp.2.2.ne hX hinj) hm
  have hr (x : ℝ) (hx : x ∈ Ioo 0 1) (y : ℝ) (hy : y ∈ Ioo 0 t) :
      F (x,2*t-y) = -F (x,y) := by
    let z := Z (x,y)
    have hrz : z ∉ L.lattice := hreg (p := (x,y)) ⟨hx,hy⟩
    have hcz : conj z ∉ L.lattice := fun h => hrz (by simpa using rhombic_conj_mem ht h)
    have hω : 2*I*t ∈ L.lattice := by
      apply (rhombic_mem_lattice_iff ht _).mpr
      refine ⟨-1,2,?_,?_⟩ <;> simp [Complex.mul_re,Complex.mul_im]
    have hz : Z (x,2*t-y) = conj z+2*I*t := by
      simp only [Z,z,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring
    dsimp only [F]
    rw [hz,hX.periodic _ hcz _ hω,hX.conjugation _ hrz,axisHelicoidSide_I_reflection]
    dsimp only [z]
    ring
  have hleft (y : ℝ) (hy : y ∈ Ioo 0 (2*t)) : F (0,y) = 0 := by
    have hx := hX.vertical_axis_zero (integerAxis_regular_points ht ha hy).1 (by simp [Complex.mul_re])
    simp [F,Z,axisHelicoidSide,hx.1,hx.2]
  have hG := harmonic_height_primitive_thetaG_zero ht ha hc hX hh
  have hmid := (harmonic_integer_axis_midpoint_data ht ha 0 hX hg).1
  have hD (y : ℝ) (hy : y ∈ Ioo 0 (2*t)) : HasDerivAt (fun x => F (x,y))
      (k y*Real.sin (δ y)) 0 := by
    have hd := (harmonic_integer_axis_side_derivative ht ha hc hG 0 hX hh hg hy).neg.div_const c
    rw [thetaGauss_axis_midpoint_eq_I ht ha 0,hmid] at hd
    simp only [Int.cast_zero,sub_zero,Pi.zero_apply] at hd
    convert hd using 1
    change -(L.weierstrassP (I*y)-L.weierstrassP a).re*Real.sin (δ y) =
      -((I*(c:ℂ)*(L.weierstrassP (I*y)-L.weierstrassP a)).im*Real.sin (δ y))/c
    simp only [Complex.mul_im,Complex.I_re,zero_mul,Complex.ofReal_im,Complex.I_im,Complex.ofReal_re,
      one_mul,zero_add,Complex.mul_re,mul_zero,sub_zero]
    field_simp
  obtain ⟨hb0,e,he,hd⟩ := harmonic_zero_branch_bottom_side_derivative ht ha hc α hX hh hg
  have h0 : F (a,0) = 0 := by simp [F,Z,hb0]
  obtain ⟨hL,hR⟩ := oriented_rectangle_edge_signs ht ha hF hn hr h0 hd he hleft hD
  have hk (y : ℝ) (hy : y ∈ Ioo 0 (2*t)) : 0 < k y :=
    neg_pos.mpr (axisRegularCoefficient_den_re_neg ht ha hy)
  have hbad := integerAxisPhase_index_positive_of_oriented_sides ht ha 0
    (fun y hy => nonpos_of_mul_nonpos_right (hL y hy) (hk y ⟨hy.1,by linarith [hy.2]⟩))
    (fun y hy => (mul_nonneg_iff_of_pos_left (hk y ⟨ht.trans hy.1,hy.2⟩)).mp (hR y hy))
  omega

theorem integer_branch_one_of_intersection_principle (hHW : RhombicHelicoidIntersectionPrinciple)
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    m = 1 := by
  rcases integer_branch_zero_or_one_of_intersection_principle hHW ht ha hc m hX hXi hh hg with hm | hm
  · subst m
    exfalso
    obtain ⟨b,hEnd,hH⟩ := harmonic_integer_end_comparison_helicoid ht ha hc 0 hX hh hg
    have hD := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc 0 hX hh hg
    have hE := harmonicTorusImmersion_closedEmbedding_of_escape hX hXi
      (integer_primitive_end_escape_and_embedding 0 ht ha hc hD).1 (rhombic_puncture_eventually_off_lattice ht)
    obtain ⟨hAx,hAz⟩ := harmonic_integer_data_contains_complete_axes ht ha hc 0 hX hh hg
    have h := hHW ht hX (integer_helicoidal_pitch_ne_zero ha hc 0) b hE
      (fun x => (harmonicTorusImmersion_range hX).symm ▸ hAx x)
      (fun z => (harmonicTorusImmersion_range hX).symm ▸ hAz z) hEnd hH
    rw [hH] at h
    apply harmonic_zero_branch_excluded_by_axis_intersection ht ha hc hX hh hg hXi
    simpa only [Int.cast_zero,sub_zero] using h
  · exact hm

/-- An embedded actual harmonic torus with both meromorphic pole orders
has the basic integer-one data after a Euclidean isometry, subject to
the published Hoffman–White intersection theorem alone. -/
theorem harmonic_meromorphic_basic_data_of_intersection_principle
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (a c : ℝ) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (fun z => R (X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z 2 =
          coordinateData t a c ht z 2) ∧
      ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z) =
          thetaGauss t a 1 z := by
  obtain ⟨a,c,m,R,ha,hc,hT,ha',hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_oriented_integer_data ht hX hhOrder hgOrder
  have hYi : Function.Injective (harmonicTorusImmersion hY) := by
    rw [harmonicTorusImmersion_space_map hX R hY]
    exact R.injective.comp hXi
  have hm := integer_branch_one_of_intersection_principle hHW ht ha hc m hY hYi hh hg
  subst m
  exact ⟨a,c,R,ha,hc,hT,ha',hR,hY,hh,hg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_meromorphic_basic_data_of_intersection_principle
