import TwoAxisHelicoid.SmoothSolidTorusSpinParity
import TwoAxisHelicoid.HelicoidalTorusSpinParity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Manifold ContDiff

/-- The geometric solid-torus input, in the smooth category and with an
actual compactified ambient product chart. This is the classical
Alexander conclusion, recorded explicitly as an external hypothesis. -/
def EmbeddedTorusBoundsSmoothSolid : Prop :=
  ∀ (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)),
    let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) → HasSmoothCompactifiedSolidTorus F

theorem helicoidal_torus_marked_arf_zero_of_solid_torus
    (hAlexander : EmbeddedTorusBoundsSmoothSolid) (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    ∀ v w, torusIntersectionModTwo v w = 1 →
      capAmbientSpinQuadratic L X v * capAmbientSpinQuadratic L X w = 0 := by
  obtain ⟨F,cs,U,hm,he,hcap,hfi,hU,hpU,hCU,hfx,hcompat⟩ :=
    smooth_marked_helicoid_cap L A hA hAi hEnd hX hXi hsm hi (puncturedGeneratorCore_isCompact L)
  have hzero := compactified_solid_torus_forces_even_arf L he.isEmbedding (fun p hp => (hcompat p hp).1)
    (fun p hp => (hcompat p hp).2.1) (hAlexander L F cs hm he hcap hfi)
  have hq : capAmbientSpinQuadratic L F = capAmbientSpinQuadratic L X := by
    classical
    unfold capAmbientSpinQuadratic
    simp only [cap_ambient_spin_closes_of_eq_near_generators L hU hCU hfx]
  intro v w hvw
  rw [cap_ambient_arf_basis L X v w hvw, ← hq]
  exact hzero

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : (C : ℂ)^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)

include ht ha hc m hC0 hC hX hp hh hg in
/-- Application of the single published geometric input to the cap of an
embedded branch. All its manifold, marking, and ambient-frame hypotheses
are derived from the immersion and the constructed cap. -/
theorem harmonic_integer_odd_of_solid_torus (hAlexander : EmbeddedTorusBoundsSmoothSolid)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1)) : Odd m := by
  let L := rhombicPeriodPair t ht
  obtain ⟨G,cs,V,hm,hclosed,hs,hi,hV,_,hCV,hfixV,hcompat⟩ :=
    harmonic_integer_embedded_cap_with_compatible_atlas ht ha hc m hX hp hh hg hXi (puncturedGeneratorCore_isCompact L)
  have hzero := compactified_solid_torus_forces_even_arf L hclosed.isEmbedding (fun p hp => (hcompat p hp).1)
    (fun p hp => (hcompat p hp).2.1) (hAlexander L G cs hm hclosed hs hi)
  have he := cap_ambient_arf_eq_line_parity ht ha hc m hC0 hC hX hp hh hg hV hfixV hCV
    (v := (1,0)) (w := (0,1)) (by decide)
  rw [← Int.not_even_iff_odd]
  intro hem
  simp only [holomorphicMultiplierSection_finrank ht m,hem,ite_true] at he
  exact zero_ne_one (hzero.symm.trans he)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_torus_marked_arf_zero_of_solid_torus
#print axioms TwoAxisHelicoid.harmonic_integer_odd_of_solid_torus
