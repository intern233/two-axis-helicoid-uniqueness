import TwoAxisHelicoid.PeriodTorusScaling

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

noncomputable def conjugatePeriodPair (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    apply LinearIndependent.pair_iff.mp L.indep a b
    have he := congrArg conj h
    simpa [Complex.real_smul] using he

theorem conjugatePeriodPair_mem_iff (L : PeriodPair) (z : ℂ) :
    z ∈ (conjugatePeriodPair L).lattice ↔ conj z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice,PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    have h := congrArg conj he
    simpa [conjugatePeriodPair] using h
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    have h := congrArg conj he
    simpa [conjugatePeriodPair] using h

noncomputable def scaledPeriodPair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c*L.ω₁
  ω₂ := c*L.ω₂
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    apply LinearIndependent.pair_iff.mp L.indep a b
    have he : c*((a : ℂ)*L.ω₁+(b : ℂ)*L.ω₂) = 0 := by
      simp only [Complex.real_smul] at h
      linear_combination h
    simpa only [Complex.real_smul] using (mul_eq_zero.mp he).resolve_left hc

theorem scaledPeriodPair_mem_iff (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    z ∈ L.lattice ↔ c*z ∈ (scaledPeriodPair L c hc).lattice := by
  rw [PeriodPair.mem_lattice,PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    simp only [scaledPeriodPair]
    rw [← he]
    ring
  · rintro ⟨m,n,he⟩
    refine ⟨m,n,?_⟩
    apply mul_left_cancel₀ hc
    change (m : ℂ)*(c*L.ω₁)+(n : ℂ)*(c*L.ω₂) = c*z at he
    calc c*((m : ℂ)*L.ω₁+(n : ℂ)*L.ω₂) = (m : ℂ)*(c*L.ω₁)+(n : ℂ)*(c*L.ω₂) := by ring
      _ = c*z := he

theorem scaledPeriodPair_mem (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    z ∈ (scaledPeriodPair L c hc).lattice ↔ c⁻¹*z ∈ L.lattice := by
  rw [scaledPeriodPair_mem_iff L c hc]
  simp [hc]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.scaledPeriodPair_mem_iff
