import TwoAxisHelicoid.ZetaAddition
import TwoAxisHelicoid.WeierstrassSecondOrder

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

theorem weierstrass_sub_ne_zero_of_sigma {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    (rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a ≠ 0 := by
  have hS (w : ℂ) (hw : w ∉ (rhombicPeriodPair t ht).lattice) : thetaSigma t w ≠ 0 :=
    mt (thetaSigma_zero_iff_lattice_of_pos ht ht w).mp hw
  have hs := thetaSigma_addition_of_pos ht ht ha hz
  have hn := div_ne_zero (mul_ne_zero (hS _ hm) (hS _ hp))
    (mul_ne_zero (pow_ne_zero 2 (hS _ hz)) (pow_ne_zero 2 (hS _ ha)))
  rw [hs] at hn
  exact sub_ne_zero.mpr (sub_ne_zero.mp hn).symm

theorem thetaZeta_weierstrass_addition {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    (thetaZeta t (z-a)-thetaZeta t z+thetaZeta t a)^2 =
      (rhombicPeriodPair t ht).weierstrassP (z-a)+
        (rhombicPeriodPair t ht).weierstrassP z+(rhombicPeriodPair t ht).weierstrassP a := by
  let L := rhombicPeriodPair t ht
  let U := fun w : ℂ => thetaZeta t (w-a)-thetaZeta t w+thetaZeta t a
  have hU : HasDerivAt U (L.weierstrassP z-L.weierstrassP (z-a)) z := by
    have hh := (((thetaZeta_hasDerivAt_of_pos ht ht hm).comp
      (h := fun w : ℂ => w-a) z ((hasDerivAt_id z).sub_const a)).sub
        (thetaZeta_hasDerivAt_of_pos ht ht hz)).add_const (thetaZeta t a)
    convert hh using 1
    · rfl
    · ring
  have hD := (((hU.mul ((rhombic_weierstrassP_hasDerivAt ht hz).sub_const (L.weierstrassP a))).const_mul 2))
  have hR := ((L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt).add_const (L.derivWeierstrassP a)
  have hmC : ContinuousAt (fun w : ℂ => w-a) z := continuousAt_id.sub continuousAt_const
  have hpC : ContinuousAt (fun w : ℂ => w+a) z := continuousAt_id.add continuousAt_const
  have he : (fun w : ℂ => 2*U w*(L.weierstrassP w-L.weierstrassP a)) =ᶠ[𝓝 z]
      fun w => L.derivWeierstrassP w+L.derivWeierstrassP a := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
      hmC.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hm),
      hpC.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hp)] with w hw hwm hwp
    exact thetaZeta_addition_cross ht ha hw hwm hwp
  have hD' : HasDerivAt (fun w : ℂ => 2*U w*(L.weierstrassP w-L.weierstrassP a))
      (2*((L.weierstrassP z-L.weierstrassP (z-a))*(L.weierstrassP z-L.weierstrassP a)+
        U z*L.derivWeierstrassP z)) z := by
    convert hD using 1
    funext w
    simp only [Pi.mul_apply]
    ring
  have hder := hD'.unique (hR.congr_of_eventuallyEq he)
  rw [rhombic_weierstrass_second_order ht hz] at hder
  have hcross := thetaZeta_addition_cross ht ha hz hm hp
  have hza := L.derivWeierstrassP_sq a ha
  have hzz := L.derivWeierstrassP_sq z hz
  have hne := weierstrass_sub_ne_zero_of_sigma ht ha hz hm hp
  change U z^2 = L.weierstrassP (z-a)+L.weierstrassP z+L.weierstrassP a
  change 2*U z*(L.weierstrassP z-L.weierstrassP a) = _ at hcross
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  linear_combination (L.weierstrassP z-L.weierstrassP a)/2*hder+
    (2*U z*(L.weierstrassP z-L.weierstrassP a)-L.derivWeierstrassP z+L.derivWeierstrassP a)/4*hcross+
    (1/4:ℂ)*(hza-hzz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_weierstrass_addition
