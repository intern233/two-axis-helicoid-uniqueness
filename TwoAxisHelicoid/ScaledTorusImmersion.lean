import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.PeriodTorusScaling
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Complex Set Topology

/-- A change in the complex marking identifies the original punctured quotient
with the quotient carrying the symmetric harmonic coordinates. -/
theorem scaled_harmonic_quotient_correspondence (L M : PeriodPair) (s : ℂ) (hs : s ≠ 0)
    (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ M.lattice) (X : PeriodTorus L → Fin 3 → ℝ)
    (hY : TwoAxisHarmonicConformalImmersion M (fun z => X (periodTorusProjection L (s⁻¹*z)))) :
    ∃ e : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus M,
      ∀ q, harmonicTorusImmersion hY (e q) = X q.1 := by
  let E := periodTorusScalingHomeomorph L M s hs hp
  have hE0 : E 0 = 0 := by change periodTorusProjection M (s*0) = 0; simp
  let e := E.subtype (p := fun q => q ≠ 0) (q := fun q => q ≠ 0)
    (fun v => by rw [← hE0, E.injective.ne_iff])
  refine ⟨e,?_⟩
  intro q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  change periodTorusProjection L z = q.1 at hz
  have he : (e q).1 = periodTorusProjection M (s*z) := by
    change E q.1 = _
    rw [← hz]
    rfl
  have hn : s*z ∉ M.lattice := fun h => (e q).2 (he.trans ((periodTorusProjection_eq_zero M _).mpr h))
  let r := puncturedPlaneProjection M ⟨s*z,hn⟩
  have hr : e q = r := Subtype.ext he
  rw [hr]
  have hy := harmonicTorusImmersion_projection hY hn
  change harmonicTorusImmersion hY r = X (periodTorusProjection L (s⁻¹*(s*z))) at hy
  simpa only [← mul_assoc,inv_mul_cancel₀ hs,one_mul,hz] using hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scaled_harmonic_quotient_correspondence
