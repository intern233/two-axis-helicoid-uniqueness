import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.SigmaAllPositive

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The unique nonpunctured point common to the two marked reflection axes
has representative one in the normalized lattice. Its ambient position is
the intersection of the two centered spatial axes. -/
theorem harmonic_axis_parameter_one {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) : X 1 = 0 := by
  let L := rhombicPeriodPair t ht
  have h1 : (1:ℂ) ∉ L.lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ) < 1) (by norm_num)
  have hr := hX.conjugation 1 h1
  have hv := hX.neg 1 h1
  have hp := hX.periodic 1 h1 (-2) (L.lattice.neg_mem L.ω₁_mem_lattice)
  rw [map_one] at hr
  rw [show (1:ℂ)+ -2 = -1 by norm_num] at hp
  rw [hp] at hv
  ext j
  fin_cases j
  · have h := congrFun hv 0
    change X 1 0 = -X 1 0 at h
    change X 1 0 = 0
    linarith
  · have h := congrFun hr 1
    change X 1 1 = -X 1 1 at h
    change X 1 1 = 0
    linarith
  · have h := congrFun hr 2
    change X 1 2 = -X 1 2 at h
    change X 1 2 = 0
    linarith

noncomputable def rhombicAxisPoint {t : ℝ} (ht : 0 < t) : PuncturedPeriodTorus (rhombicPeriodPair t ht) :=
  ⟨periodTorusProjection _ 1, fun h => (real_not_mem_rhombic_lattice_of_pos ht
    (by norm_num : (0:ℝ) < 1) (by norm_num)) (by simpa using (periodTorusProjection_eq_zero _ 1).mp h)⟩

theorem harmonicTorus_axis_point {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) :
    harmonicTorusImmersion hX (rhombicAxisPoint ht) = 0 := by
  have h1 : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ) < 1) (by norm_num)
  exact (harmonicTorusImmersion_projection hX h1).trans (harmonic_axis_parameter_one ht hX)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonicTorus_axis_point
