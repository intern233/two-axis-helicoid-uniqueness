import TwoAxisHelicoid.CapOrthonormalSpin
import TwoAxisHelicoid.HolomorphicMultiplierParity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Matrix ContDiff Manifold

/-- The classical embedded-torus parity theorem in marked coordinates.
The smooth structure can vary; the two charts along the marked curves
must agree smoothly with the standard marking. The spin test uses the
actual orthonormal frames of the spatial embedding. -/
def EmbeddedTorusAmbientSpinParity : Prop :=
  ∀ (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)), let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) →
    IsClosedEmbedding F → ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) →
    (∀ p ∈ Subtype.val '' puncturedGeneratorCore L,
      ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) p ∧
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) p) →
      capAmbientSpinQuadratic L F (1,0) * capAmbientSpinQuadratic L F (0,1) = 0

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : (C : ℂ)^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    {U : Set (PeriodTorus (rhombicPeriodPair t ht))} (hU : IsOpen U)
    (hfix : ∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore (rhombicPeriodPair t ht) ⊆ U)

include ht ha hc m hC0 hC hX hp hh hg hU hfix hcore in
theorem cap_ambient_generator_spin_iff (i : Fin 2) :
    CapGeneratorAmbientSpinCloses (rhombicPeriodPair t ht) F i ↔ i = 0 ∨ Even m := by
  rw [← cap_generator_closed_lift_iff ht ha hc m hC0 hC hX hp hh hg hU hfix hcore]
  apply ambient_generator_spin_closes_iff
  intro r
  exact ⟨_,_,generator_spin_normalization_positive ht ha m hC0 i r,
    harmonic_integer_cap_adapted_generator_frame ht ha hc m hC0 hC hX hp hh hg hU hfix hcore i r⟩

include ht ha hc m hC0 hC hX hp hh hg hU hfix hcore in
theorem cap_ambient_arf_eq_line_parity {v w : ZMod 2 × ZMod 2} (hvw : torusIntersectionModTwo v w = 1) :
    capAmbientSpinQuadratic (rhombicPeriodPair t ht) F v * capAmbientSpinQuadratic (rhombicPeriodPair t ht) F w =
      (Module.finrank ℂ (holomorphicMultiplierSections (rhombicPeriodPair t ht)
        (latticeSpinParity (rhombicPeriodPair t ht) m)) : ZMod 2) := by
  classical
  have he : capAmbientSpinQuadratic (rhombicPeriodPair t ht) F = capGeneratorQuadratic (rhombicPeriodPair t ht) F := by
    unfold capAmbientSpinQuadratic capGeneratorQuadratic
    simp only [cap_ambient_generator_spin_iff ht ha hc m hC0 hC hX hp hh hg hU hfix hcore,
      cap_generator_closed_lift_iff ht ha hc m hC0 hC hX hp hh hg hU hfix hcore]
  rw [he,capGeneratorQuadratic_eq_integer ht ha hc m hC0 hC hX hp hh hg hU hfix hcore]
  exact integerGeneratorQuadratic_arf_eq_line_sections ht m hvw

include ht ha hc m hC0 hC hX hp hh hg in
/-- Application of the single published geometric input to the cap of an
embedded branch. All its manifold, marking, and ambient-frame hypotheses
are derived from the immersion and the constructed cap. -/
theorem harmonic_integer_odd_of_embedded_torus_parity (hParity : EmbeddedTorusAmbientSpinParity)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1)) : Odd m := by
  let L := rhombicPeriodPair t ht
  obtain ⟨G,cs,V,hm,hclosed,hs,hi,hV,_,hCV,hfixV,hcompat⟩ :=
    harmonic_integer_embedded_core_cap ht ha hc m hX hp hh hg hXi (puncturedGeneratorCore_isCompact L)
  have hzero := hParity L G cs hm hclosed hs hi (fun p hp => hcompat p (hCV hp))
  have he := cap_ambient_arf_eq_line_parity ht ha hc m hC0 hC hX hp hh hg hV hfixV hCV
    (v := (1,0)) (w := (0,1)) (by decide)
  rw [← Int.not_even_iff_odd]
  intro hem
  simp only [holomorphicMultiplierSection_finrank ht m,hem,ite_true] at he
  exact zero_ne_one (hzero.symm.trans he)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.cap_ambient_arf_eq_line_parity
#print axioms TwoAxisHelicoid.harmonic_integer_odd_of_embedded_torus_parity
