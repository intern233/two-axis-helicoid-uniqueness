import TwoAxisHelicoid.ZetaPoleRegular
import TwoAxisHelicoid.RealPrimitivePeriods
import TwoAxisHelicoid.SimplePoleInfinity
import TwoAxisHelicoid.LatticePoleSets

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
attribute [local irreducible] thetaZeta zetaPoleRegular

noncomputable def actualComplexHeight (t a c : ℝ) (ht : 0 < t) (z : ℂ) : ℂ :=
  -I*(c : ℂ)*(thetaZeta t z+(rhombicPeriodPair t ht).weierstrassP a*z)

noncomputable def actualHeightRegular (t a c : ℝ) (ht : 0 < t) (z : ℂ) : ℂ :=
  -I*(c : ℂ)*(zetaPoleRegular t z+(rhombicPeriodPair t ht).weierstrassP a*z)

theorem actualComplexHeight_hasDerivAt {t a c : ℝ} (ht : 0 < t)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (actualComplexHeight t a c ht) (coordinateData t a c ht z 2) z := by
  have hd := ((thetaZeta_hasDerivAt_of_pos ht ht hz).add
    ((hasDerivAt_id z).const_mul ((rhombicPeriodPair t ht).weierstrassP a))).const_mul (-I*(c : ℂ))
  convert hd using 1
  · rfl
  · change I*(c : ℂ)*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) =
      -I*(c : ℂ)*(-(rhombicPeriodPair t ht).weierstrassP z+(rhombicPeriodPair t ht).weierstrassP a*1)
    ring

theorem actualHeightRegular_analyticAt_zero {t a c : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (actualHeightRegular t a c ht) 0 := by
  unfold actualHeightRegular
  exact (analyticAt_const.mul ((zetaPoleRegular_analyticAt ht (Or.inr rfl)).add
    (analyticAt_const.mul analyticAt_id)))

theorem actualComplexHeight_principal_part {t a c : ℝ} (ht : 0 < t)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    actualComplexHeight t a c ht z =
      simplePoleCoordinate (-I*(c : ℂ)) (actualHeightRegular t a c ht) z := by
  unfold actualComplexHeight simplePoleCoordinate actualHeightRegular
  rw [thetaZeta_eq_inv_add_regular ht hz]
  ring

theorem rhombic_puncture_eventually_off_lattice {t : ℝ} (ht : 0 < t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ (rhombicPeriodPair t ht).lattice := by
  have h := latticePoleSet_punctured_avoids (rhombicPeriodPair t ht) (finite_singleton (0 : ℂ)) 0
  filter_upwards [h] with z hz
  simpa [latticePoleSet] using hz

theorem actualComplexHeight_tendsto {t a c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    Tendsto (actualComplexHeight t a c ht) (𝓝[≠] 0) (cobounded ℂ) := by
  apply (simplePoleCoordinate_tendsto
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr hc))
    (actualHeightRegular_analyticAt_zero (a := a) (c := c) ht)).congr'
  filter_upwards [rhombic_puncture_eventually_off_lattice ht] with z hz
  exact (actualComplexHeight_principal_part ht hz).symm

theorem actual_complex_height_real_primitive {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ b : ℝ, ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      X z 2 = (actualComplexHeight t a c ht z).re+b := by
  have hd z hz : HasFDerivAt (fun w => (actualComplexHeight t a c ht w).re)
      (realCoefficientDerivative (coordinateData t a c ht z 2)) z :=
    Complex.reCLM.hasFDerivAt.comp z ((actualComplexHeight_hasDerivAt ht hz).hasFDerivAt.restrictScalars ℝ)
  exact (rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
    (rhombic_punctured_plane_isConnected ht).2
    (fun z hz => (actual_coordinate_primitive_component ht hX hz 2).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(actual_coordinate_primitive_component ht hX hz 2).fderiv,(hd z hz).fderiv])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualComplexHeight_tendsto
#print axioms TwoAxisHelicoid.actual_complex_height_real_primitive
