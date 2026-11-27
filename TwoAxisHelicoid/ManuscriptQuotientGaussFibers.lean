import TwoAxisHelicoid.ManuscriptSphericalGaussFibers
import TwoAxisHelicoid.TorusSphericalGaussRigidity
import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology OnePoint

/-- The two fibers of the sphere-valued Gauss map computed from the position
on the punctured torus, in the marking of the covering immersion. -/
theorem manuscript_quotient_spherical_gauss_fibers {t a : ℝ} {ht : 0 < t}
    {Z : ℂ → Fin 3 → ℝ} (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z)
    (fibers : PhysicalSphericalGaussDivisor t a ht Z) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    let L := rhombicPeriodPair t ht
    let G := torusSphericalGauss L (harmonicTorusImmersion hZ)
    (G q = (↑(0 : ℂ) : OnePoint ℂ) ↔ q.1 = periodTorusProjection L (a : ℂ)) ∧
      (G q = ∞ ↔ q.1 = periodTorusProjection L (-(a : ℂ))) := by
  intro L G
  obtain ⟨⟨z,hz⟩,rfl⟩ := puncturedPlaneProjection_surjective L q
  have forms : torusImmersionForms L (harmonicTorusImmersion hZ) z = immersionComplexCoefficient Z z := by
    funext j
    have agree : (fun w => puncturedTorusPullback L (harmonicTorusImmersion hZ) w j) =ᶠ[𝓝 z]
        (fun w => Z w j) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w ∉ L.lattice at hw
      have point : puncturedTorusPullback L (harmonicTorusImmersion hZ) w =
          harmonicTorusImmersion hZ (puncturedPlaneProjection L ⟨w,hw⟩) := by
        unfold puncturedTorusPullback
        rw [dite_eq_left hw]
      exact congrFun (point.trans (harmonicTorusImmersion_projection hZ hw)) j
    change scalarComplexCoefficient (fun w => puncturedTorusPullback L (harmonicTorusImmersion hZ) w j) z =
      scalarComplexCoefficient (fun w => Z w j) z
    unfold scalarComplexCoefficient
    rw [agree.fderiv_eq (𝕜 := ℝ)]
  change (sphericalNullGauss (torusImmersionForms L (harmonicTorusImmersion hZ) z) =
      (↑(0 : ℂ) : OnePoint ℂ) ↔ periodTorusProjection L z = periodTorusProjection L (a : ℂ)) ∧
    (sphericalNullGauss (torusImmersionForms L (harmonicTorusImmersion hZ) z) = ∞ ↔
      periodTorusProjection L z = periodTorusProjection L (-(a : ℂ)))
  rw [forms]
  have pos : z - (a : ℂ) ∈ L.lattice ↔ periodTorusProjection L z = periodTorusProjection L (a : ℂ) :=
    (periodTorusProjection_eq_iff L (a : ℂ) z).symm.trans eq_comm
  have neg : z + (a : ℂ) ∈ L.lattice ↔ periodTorusProjection L z = periodTorusProjection L (-(a : ℂ)) := by
    simpa only [sub_neg_eq_add] using (periodTorusProjection_eq_iff L (-(a : ℂ)) z).symm.trans eq_comm
  exact ⟨((fibers.2.2 z hz).1).trans pos,((fibers.2.2 z hz).2).trans neg⟩

/-- Pointwise on the original carrier in its marked rigid placement.
The equality of position maps is the pointwise field of the original spin cap. -/
theorem manuscript_rigidly_placed_gauss_fibers {M : Type*} {t a : ℝ} {ht : 0 < t}
    {Z : ℂ → Fin 3 → ℝ} (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z)
    (fibers : PhysicalSphericalGaussDivisor t a ht Z)
    (e : M ≃ PuncturedPeriodTorus (rhombicPeriodPair t ht)) (position : M → Fin 3 → ℝ)
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (same : ∀ x, harmonicTorusImmersion hZ (e x) = R (position x)) (x : M) :
    let L := rhombicPeriodPair t ht
    let G := torusSphericalGauss L (fun q => R (position (e.symm q)))
    (G (e x) = (↑(0 : ℂ) : OnePoint ℂ) ↔ (e x).1 = periodTorusProjection L (a : ℂ)) ∧
      (G (e x) = ∞ ↔ (e x).1 = periodTorusProjection L (-(a : ℂ))) := by
  have placed : (fun q => R (position (e.symm q))) = harmonicTorusImmersion hZ := by
    funext q
    simpa only [e.apply_symm_apply] using (same (e.symm q)).symm
  dsimp only
  rw [placed]
  exact manuscript_quotient_spherical_gauss_fibers hZ fibers (e x)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_quotient_spherical_gauss_fibers
#print axioms TwoAxisHelicoid.manuscript_rigidly_placed_gauss_fibers
