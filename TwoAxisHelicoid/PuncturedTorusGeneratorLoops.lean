import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.PeriodTorusConjugation
import Mathlib.Topology.Path

namespace TwoAxisHelicoid
open Complex Set Topology
set_option maxHeartbeats 1000000

noncomputable def periodPairCenter (L : PeriodPair) : ℂ :=
  (1/2 : ℝ) • L.ω₁+(1/2 : ℝ) • L.ω₂

noncomputable def periodBasisLine (L : PeriodPair) (i : Fin 2) (s : ℝ) : ℂ :=
  periodPairCenter L+s • L.basis i

theorem periodBasisLine_coordinates (L : PeriodPair) (i j : Fin 2) (s : ℝ) :
    L.basis.repr (periodBasisLine L i s) j = 1/2+if i = j then s else 0 := by
  unfold periodBasisLine periodPairCenter
  rw [← L.basis_zero,← L.basis_one]
  fin_cases i <;> fin_cases j <;>
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul] <;> norm_num

theorem periodPair_lattice_coordinate (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice)
    (j : Fin 2) : ∃ n : ℤ, L.basis.repr z j = (n : ℝ) := by
  obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hz
  have he : (m : ℂ)*L.ω₁+(n : ℂ)*L.ω₂ =
      (m : ℝ) • L.basis 0+(n : ℝ) • L.basis 1 := by
    simp [Complex.real_smul]
  rw [he]
  fin_cases j
  · refine ⟨m,?_⟩
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul]
    norm_num
  · refine ⟨n,?_⟩
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul]
    norm_num

theorem periodBasisLine_not_mem_lattice (L : PeriodPair) (i : Fin 2) (s : ℝ) :
    periodBasisLine L i s ∉ L.lattice := by
  intro hz
  have hn : ∃ n : ℤ, (1/2 : ℝ) = n := by
    fin_cases i
    · obtain ⟨n,hn⟩ := periodPair_lattice_coordinate L hz 1
      exact ⟨n,by simpa [periodBasisLine_coordinates] using hn⟩
    · obtain ⟨n,hn⟩ := periodPair_lattice_coordinate L hz 0
      exact ⟨n,by simpa [periodBasisLine_coordinates] using hn⟩
  obtain ⟨n,hn⟩ := hn
  have he : (2 : ℝ)*n = 1 := by linarith
  have hi : (2 : ℤ)*n = 1 := by exact_mod_cast he
  omega

noncomputable def puncturedBasisLine (L : PeriodPair) (i : Fin 2) :
    ℝ → PuncturedLatticePlane L :=
  fun s => ⟨periodBasisLine L i s,periodBasisLine_not_mem_lattice L i s⟩

theorem puncturedBasisLine_continuous (L : PeriodPair) (i : Fin 2) :
    Continuous (puncturedBasisLine L i) := by
  apply Continuous.subtype_mk
  change Continuous (fun s : ℝ => periodPairCenter L+s • L.basis i)
  fun_prop

theorem periodBasisLine_add_one (L : PeriodPair) (i : Fin 2) (s : ℝ) :
    periodBasisLine L i (s+1) = periodBasisLine L i s+L.basis i := by
  simp only [periodBasisLine,add_smul,one_smul,add_assoc]

theorem periodBasisLine_periodic_projection (L : PeriodPair) (i : Fin 2) :
    Function.Periodic (puncturedPlaneProjection L ∘ puncturedBasisLine L i) 1 := by
  intro s
  apply Subtype.ext
  change periodTorusProjection L (periodBasisLine L i (s+1)) =
    periodTorusProjection L (periodBasisLine L i s)
  rw [periodBasisLine_add_one]
  apply periodTorusProjection_add_lattice
  fin_cases i
  · change L.basis 0 ∈ L.lattice
    rw [L.basis_zero]
    exact L.ω₁_mem_lattice
  · change L.basis 1 ∈ L.lattice
    rw [L.basis_one]
    exact L.ω₂_mem_lattice

noncomputable def puncturedTorusCenter (L : PeriodPair) : PuncturedPeriodTorus L :=
  puncturedPlaneProjection L (puncturedBasisLine L 0 0)

/-- Actual closed curves avoiding the puncture, whose plane lifts have
the two prescribed lattice generators as their endpoint displacements. -/
noncomputable def puncturedTorusGeneratorLoop (L : PeriodPair) (i : Fin 2) :
    Path (puncturedTorusCenter L) (puncturedTorusCenter L) :=
  Path.ofLine ((puncturedPlaneProjection_continuous L).comp
    (puncturedBasisLine_continuous L i)).continuousOn
    (by apply Subtype.ext; simp [puncturedTorusCenter,puncturedPlaneProjection,
      puncturedBasisLine,periodBasisLine])
    (by rw [show (1 : ℝ) = 0+1 from by norm_num,
        periodBasisLine_periodic_projection L i]
        apply Subtype.ext
        simp [puncturedTorusCenter,puncturedPlaneProjection,puncturedBasisLine,periodBasisLine])

noncomputable def puncturedGeneratorCore (L : PeriodPair) : Set (PuncturedPeriodTorus L) :=
  range (puncturedTorusGeneratorLoop L 0) ∪ range (puncturedTorusGeneratorLoop L 1)

theorem puncturedGeneratorCore_isCompact (L : PeriodPair) : IsCompact (puncturedGeneratorCore L) :=
  (isCompact_range (puncturedTorusGeneratorLoop L 0).continuous).union
    (isCompact_range (puncturedTorusGeneratorLoop L 1).continuous)

theorem puncturedTorusGeneratorLoop_mem_core (L : PeriodPair) (i : Fin 2)
    (s : unitInterval) : puncturedTorusGeneratorLoop L i s ∈ puncturedGeneratorCore L := by
  fin_cases i
  · exact Or.inl ⟨s,rfl⟩
  · exact Or.inr ⟨s,rfl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodBasisLine_not_mem_lattice
#print axioms TwoAxisHelicoid.puncturedGeneratorCore_isCompact
