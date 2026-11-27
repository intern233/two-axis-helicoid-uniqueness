import TwoAxisHelicoid.OriginalClassificationAfterUniformization
import TwoAxisHelicoid.LopezRosHolomorphicCoordinates

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology Manifold ContDiff OnePoint

/-- On every marked cap supplied by the original spin argument, the actual
physical immersion in its cap coordinates has the certified parameter pair
and the simple Gauss divisor. The horizontal and vertical differentials fix
the values at the two finite marked points by continuity. -/
theorem spin_cap_parameters_and_gauss_divisor (s : OriginalPositionallyAsymptoticHelicoid)
    [ChartedSpace ℂ s.carrier] {t a c : ℝ} {ht : 0 < t} {m : ℤ}
    {e : s.carrier ≃ₜ PuncturedPeriodTorus (rhombicPeriodPair t ht)}
    {R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)} {Z : ℂ → Fin 3 → ℝ}
    {hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z}
    (cap : OriginalMarkedSpinCapData s a c m e R Z hZ) :
    t = certifiedClosedParameters.t ∧ a = certifiedClosedParameters.a ∧
      GaussZeroPoleData t a ht (immersionGaussMap Z) := by
  obtain ⟨_,_,_,_,_,ha,hc,_,_,hh,hg,_,hm,_⟩ := cap
  subst m
  have basic (z : ℂ) (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) Z z) = 1 * thetaGauss t a 1 z := by
    simpa only [one_mul] using hg z hz
  have hpair := harmonic_basic_data_parameters_certified ht ha hc norm_one hZ hh basic
  have hd := harmonic_basic_gauss_data_has_coordinate_differential ht ha hc norm_one hZ hh basic
  have phase (z : ℂ) : phasedCoordinateData t a c ht 1 z = coordinateData t a c ht z := by
    funext j
    fin_cases j <;> simp [phasedCoordinateData,complexVerticalRotation]
  have forms : HasTwoAxisHelicoidCoordinateDifferential Z t a c ht := by
    intro z hz
    simpa only [phase] using hd z hz
  obtain ⟨G,H⟩ := periodic_actual_primitive_period_equations ht ha hc forms hZ.periodic
  have model := actual_global_conformal_harmonic_immersion ht ha hc G H
  refine ⟨hpair.1,hpair.2,GaussZeroPoleData.congr_off_lattice ht ha
    (closed_immersion_gauss_divisor ht ha hc G H) ?_⟩
  intro z hz
  apply congrArg nullGauss
  apply nullRealDerivative_injective_coefficients
  have d := forms z hz
  have d' := (model.2.2.2 z hz).1
  exact ((immersionComplexCoefficient_hasFDerivAt d.differentiableAt).unique d).trans
    ((immersionComplexCoefficient_hasFDerivAt d'.differentiableAt).unique d').symm

/-- A single certified punctured-torus marking carries the original spatial
spin cap, the physical two-axis intersection, the actual derivative Gauss
divisor, and the biholomorphic filling at the end. -/
def HasCertifiedSpinCapGaussMarking (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  let p := certifiedClosedParameters
  ∃ S : ChartedSpace ℂ s.carrier, let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
    (∀ d ∈ atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
    ∃ (e : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (Z : ℂ → Fin 3 → ℝ)
      (hZ : TwoAxisHarmonicConformalImmersion certifiedPeriodPair Z) (c : ℝ),
      OriginalMarkedSpinCapData s p.a c 1 e R Z hZ ∧
      s.position (e.symm (rhombicAxisPoint p.height_pos)) = ![0,0,s.axes.horizontalPoint 2] ∧
      GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap Z) ∧
      ∃ T : ChartedSpace ℂ (OnePoint s.carrier), let _ := T
        IsManifold 𝓘(ℂ,ℂ) ω (OnePoint s.carrier) ∧
        ∃ H : OnePoint s.carrier ≃ₜ PeriodTorus certifiedPeriodPair, H OnePoint.infty = 0 ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
          ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : s.carrier → OnePoint s.carrier) ∧
          ∀ x : s.carrier, H (x : OnePoint s.carrier) = (e x).1

theorem certified_spin_cap_gauss_marking_of_pointed_cap (s : OriginalPositionallyAsymptoticHelicoid)
    (given : HasPointedOriginalSpinBranchCap s) : HasCertifiedSpinCapGaussMarking s := by
  obtain ⟨S,man,charts,t,ht,a,c,m,e,R,Z,hZ,_,cross,cap⟩ := given
  let _ := S
  let _ := man
  obtain ⟨et,ea,divisor⟩ := spin_cap_parameters_and_gauss_divisor s cap
  have capParts := cap
  obtain ⟨he,_,_,_,_,_,_,_,_,_,_,_,hm,_⟩ := capParts
  subst m
  subst t
  subst a
  exact ⟨S,man,charts,e,R,Z,hZ,c,cap,cross,divisor,punctured_biholomorphic_identification_fills e he⟩

theorem original_graph_certified_spin_cap_gauss_marking (s : OriginalHelicoidRepresentative) :
    HasCertifiedSpinCapGaussMarking s.toPositional :=
  certified_spin_cap_gauss_marking_of_pointed_cap s.toPositional (original_graph_poles_cap_and_index s).2.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spin_cap_parameters_and_gauss_divisor
#print axioms TwoAxisHelicoid.original_graph_certified_spin_cap_gauss_marking
