import TwoAxisHelicoid.QuaternionSpinPullback
import TwoAxisHelicoid.WeierstrassFrameLift
import TwoAxisHelicoid.SpinorActualDifferential

namespace TwoAxisHelicoid
open Complex Set

noncomputable def weierstrassTorusFrame {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedPeriodTorus (rhombicPeriodPair t ht) → OrthonormalTangentPair :=
  equivariantTorusFrame (rhombicPeriodPair t ht) (weierstrassUnitLift ht ha m hC)

theorem weierstrassTorusFrame_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    Continuous (weierstrassTorusFrame ht ha m hC) :=
  equivariantTorusFrame_continuous _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
    (weierstrassUnitLift_continuous ht ha m hC)

theorem weierstrassTorusFrame_projection {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (z : PuncturedLatticePlane (rhombicPeriodPair t ht)) :
    weierstrassTorusFrame ht ha m hC (puncturedPlaneProjection _ z) =
      unitSpinorTangentFrame (weierstrassUnitLift ht ha m hC z) :=
  equivariantTorusFrame_projection _ _ _ (weierstrassUnitLift_equivariant ht ha m hC) z

/-- The whole-torus sign character restricts to the actual standard
quaternion spin cover of the normalized Weierstrass tangent frame. -/
noncomputable def weierstrassSpinCoverHomeomorph {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    PuncturedSignCover (rhombicPeriodPair t ht) (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ
      QuaternionFramePullback (weierstrassTorusFrame ht ha m hC) :=
  signCoverQuaternionHomeomorph _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
    (weierstrassUnitLift_continuous ht ha m hC)

theorem weierstrassSpinCoverHomeomorph_base {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0)
    (q : PuncturedSignCover (rhombicPeriodPair t ht) (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    (weierstrassSpinCoverHomeomorph ht ha m hC q).1.1 = puncturedSignCoverProjection _ _ q :=
  signCoverQuaternionHomeomorph_base _ _ _ (weierstrassUnitLift_equivariant ht ha m hC)
    (weierstrassUnitLift_continuous ht ha m hC) q

/-- This frame is proved to be the normalized derivative frame of the
actual harmonic conformal immersion, including its two height critical points. -/
theorem harmonic_integer_torus_frame_derivative
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (z : PuncturedLatticePlane (rhombicPeriodPair t ht)) :
    (weierstrassTorusFrame ht ha m hC0 (puncturedPlaneProjection _ z)).1 =
      ((spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ • fderiv ℝ X z.1 1,
       (spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ • fderiv ℝ X z.1 I) := by
  rw [weierstrassTorusFrame_projection]
  rw [(harmonic_integer_data_has_spinor_differential ht ha hc m hC hX hh hg z.1 z.2).fderiv]
  exact weierstrassUnitLift_vectors ht ha m hC0 z

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassSpinCoverHomeomorph
#print axioms TwoAxisHelicoid.harmonic_integer_torus_frame_derivative

