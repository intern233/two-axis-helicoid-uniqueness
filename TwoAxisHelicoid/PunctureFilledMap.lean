import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology ComplexConjugate

/-- A harmless total representative: only the omitted lattice points are
assigned zero. Its restriction to the actual punctured surface is unchanged. -/
noncomputable def punctureFilledMap (L : PeriodPair) (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ := by
  classical
  exact if z ∈ L.lattice then 0 else X z

theorem punctureFilledMap_eq {L : PeriodPair} {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hz : z ∉ L.lattice) : punctureFilledMap L X z = X z := by
  simp [punctureFilledMap,hz]

theorem punctureFilledMap_eventuallyEq {L : PeriodPair} {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hz : z ∉ L.lattice) : punctureFilledMap L X =ᶠ[𝓝 z] X := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  exact punctureFilledMap_eq hw

theorem punctureFilledMap_periodic {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hp : ∀ z ∉ L.lattice, ∀ ω ∈ L.lattice, X (z+ω) = X z) :
    ∀ z ω, ω ∈ L.lattice → punctureFilledMap L X (z+ω) = punctureFilledMap L X z := by
  intro z ω hω
  have he : z+ω ∈ L.lattice ↔ z ∈ L.lattice := by
    constructor
    · intro h
      simpa using L.lattice.sub_mem h hω
    · exact fun h => L.lattice.add_mem h hω
  by_cases hz : z ∈ L.lattice
  · simp [punctureFilledMap,hz,he.mpr hz]
  · rw [punctureFilledMap_eq (fun h => hz (he.mp h)),punctureFilledMap_eq hz]
    exact hp z hz ω hω

theorem punctureFilledMap_coefficient {L : PeriodPair} {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L (punctureFilledMap L X) z = puncturedImmersionCoefficient L X z := by
  rw [puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hz]
  ext j
  have he : (fun w => punctureFilledMap L X w j) =ᶠ[𝓝 z] (fun w => X w j) :=
    (punctureFilledMap_eventuallyEq hz).mono (fun _ h => congrFun h j)
  simp only [immersionComplexCoefficient,scalarComplexCoefficient,he.fderiv_eq]

theorem TwoAxisHarmonicConformalImmersion.punctureFilled
    {L : PeriodPair} (hL : ConjugationInvariantLattice L) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) :
    TwoAxisHarmonicConformalImmersion L (punctureFilledMap L X) where
  differentiable z hz := (hX.differentiable z hz).congr_of_eventuallyEq (punctureFilledMap_eventuallyEq hz)
  harmonic z hz j := (harmonicAt_congr_nhds
    ((punctureFilledMap_eventuallyEq hz).mono (fun _ h => congrFun h j))).mpr (hX.harmonic z hz j)
  conformal z hz := by
    have he j : fderiv ℝ (fun w => punctureFilledMap L X w j) z = fderiv ℝ (fun w => X w j) z := by
      have hh : (fun w => punctureFilledMap L X w j) =ᶠ[𝓝 z] (fun w => X w j) :=
        (punctureFilledMap_eventuallyEq hz).mono (fun _ h => congrFun h j)
      exact hh.fderiv_eq
    simpa only [ConformalCoordinateDerivatives,he] using hX.conformal z hz
  immersion z hz := by
    rw [(punctureFilledMap_eventuallyEq hz).fderiv_eq]
    exact hX.immersion z hz
  periodic z _hz ω hω := punctureFilledMap_periodic hX.periodic z ω hω
  neg z hz := by
    rw [punctureFilledMap_eq (by simpa using hz),punctureFilledMap_eq hz]
    exact hX.neg z hz
  conjugation z hz := by
    have hcz : conj z ∉ L.lattice := fun h => hz (by simpa using hL (conj z) h)
    rw [punctureFilledMap_eq hcz,punctureFilledMap_eq hz]
    exact hX.conjugation z hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.punctureFilled
