import TwoAxisHelicoid.SphericalNullGauss
import TwoAxisHelicoid.IntrinsicGaussPhaseRigidity

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology OnePoint

/-- The sphere-valued Gauss map on the punctured quotient, computed from
the derivative of its actual position map in a marked conformal chart. -/
noncomputable def torusSphericalGauss (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (q : PuncturedPeriodTorus L) : OnePoint ℂ :=
  periodTorusLift L (fun z => sphericalNullGauss (torusImmersionForms L X z))
    (fun z ω hω => congrArg sphericalNullGauss (torusImmersionForms_periodic L X z ω hω)) q.1

theorem torusSphericalGauss_continuous (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hi : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z)) :
    Continuous (torusSphericalGauss L X) := by
  obtain ⟨ha,hn,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  apply periodTorusLift_continuous_punctured
  intro z hz
  apply sphericalNullGauss_continuousAt (fun j => (ha z hz j).continuousAt)
  · intro he
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    apply hi z hz
    have hd : fderiv ℝ (puncturedTorusPullback L X) z = nullRealDerivative (torusImmersionForms L X z) := (hD z hz).fderiv
    rw [hd,he]
    funext j
    simp
  · filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact hn w hw

/-- A global rigid motion gives the corresponding spherical rotation at
every point of the quotient, including vertical normals at either pole. -/
theorem torusSphericalGauss_rotate (L : PeriodPair) (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    {c : ℂ} (hc : ‖c‖ = 1) {d : Fin 3 → ℝ} (H : ∀ q, Y q = verticalRotation c (X q)+d) (q : PuncturedPeriodTorus L) :
    torusSphericalGauss L Y q = OnePoint.map (c*·) (torusSphericalGauss L X q) := by
  obtain ⟨⟨z,hz⟩,rfl⟩ := puncturedPlaneProjection_surjective L q
  apply sphericalNullGauss_of_rotated_real_derivative hc
  have hD (Z : PuncturedPeriodTorus L → Fin 3 → ℝ)
      (hZ : ∀ u ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Z w j) u) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L Z) u) :=
    (torusImmersionForms_regular L Z (fun u hu => (hZ u hu).1) (fun u hu => (hZ u hu).2)).2.2 z hz
  have he : (torusFilledPosition L Y ∘ periodTorusProjection L) =ᶠ[𝓝 z]
      (fun u => verticalRotation c ((torusFilledPosition L X ∘ periodTorusProjection L) u)+d) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    let q := puncturedPlaneProjection L ⟨w,hw⟩
    change torusFilledPosition L Y q.1 = verticalRotation c (torusFilledPosition L X q.1)+d
    simpa only [torusFilledPosition_eq] using H q
  exact (hD Y hY).unique ((((verticalRotation c).hasFDerivAt.comp z (hD X hX)).add_const d).congr_of_eventuallyEq he)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torusSphericalGauss_continuous
#print axioms TwoAxisHelicoid.torusSphericalGauss_rotate
