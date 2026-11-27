import TwoAxisHelicoid.FlatHolomorphicSections
import Mathlib.Analysis.SpecificLimits.Normed

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

def PreservesPeriodLattice (L : PeriodPair) (c : ℂ) : Prop :=
  ∀ z ∈ L.lattice, c*z ∈ L.lattice

def PeriodLatticeAutomultiplier (L : PeriodPair) (c : ℂ) : Prop :=
  c ≠ 0 ∧ PreservesPeriodLattice L c ∧ PreservesPeriodLattice L c⁻¹

theorem period_lattice_multiplier_norm_ge_one (L : PeriodPair) {c : ℂ}
    (hc : c ≠ 0) (hL : PreservesPeriodLattice L c) : 1 ≤ ‖c‖ := by
  by_contra hn
  have hn' : ‖c‖ < 1 := lt_of_not_ge hn
  have hne : L.ω₁ ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using L.indep.ne_zero 0
  have hnh : ({(0 : L.lattice)} : Set L.lattice) ∈ 𝓝 (0 : L.lattice) :=
    (isOpen_discrete _).mem_nhds (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnh
  have hm (n : ℕ) : c^n*L.ω₁ ∈ L.lattice := by
    induction n with
    | zero => simpa using L.ω₁_mem_lattice
    | succ n ih =>
      simpa only [pow_succ,mul_assoc,mul_comm c,mul_left_comm] using hL _ ih
  have htend : Tendsto (fun n : ℕ => c^n*L.ω₁) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn').mul_const L.ω₁
  obtain ⟨n,hn⟩ := (htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)).exists
  have hsub : (⟨c^n*L.ω₁,hm n⟩ : L.lattice) ∈ ball (0 : L.lattice) ε := by
    exact hn
  have he := hball hsub
  have hz : c^n*L.ω₁ = 0 := congrArg Subtype.val (mem_singleton_iff.mp he)
  exact (mul_ne_zero (pow_ne_zero n hc) hne) hz

theorem period_lattice_automultiplier_norm (L : PeriodPair) {c : ℂ}
    (hc : PeriodLatticeAutomultiplier L c) : ‖c‖ = 1 := by
  have h₁ := period_lattice_multiplier_norm_ge_one L hc.1 hc.2.1
  have h₂ := period_lattice_multiplier_norm_ge_one L (inv_ne_zero hc.1) hc.2.2
  rw [norm_inv] at h₂
  have hp : 0 < ‖c‖ := norm_pos_iff.mpr hc.1
  have hu : ‖c‖ ≤ 1 := by
    have h := (le_div_iff₀ hp).mp (show 1 ≤ 1/‖c‖ by simpa using h₂)
    simpa using h
  exact le_antisymm hu h₁

/-- The possible linear parts of puncture-fixing complex-torus automorphisms
form a finite set. This statement is for every complex period lattice. -/
theorem period_lattice_automultipliers_finite (L : PeriodPair) :
    {c : ℂ | PeriodLatticeAutomultiplier L c}.Finite := by
  have hne : L.ω₁ ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using L.indep.ne_zero 0
  have hfinite := (isCompact_closedBall (0 : L.lattice) ‖L.ω₁‖).finite_of_discrete
  apply (hfinite.image (fun z : L.lattice => (z : ℂ)/L.ω₁)).subset
  intro c hc
  let z : L.lattice := ⟨c*L.ω₁,hc.2.1 _ L.ω₁_mem_lattice⟩
  refine ⟨z,?_,?_⟩
  · change dist z 0 ≤ ‖L.ω₁‖
    rw [dist_zero_right]
    change ‖c*L.ω₁‖ ≤ ‖L.ω₁‖
    rw [norm_mul,period_lattice_automultiplier_norm L hc,one_mul]
  · exact mul_div_cancel_right₀ c hne

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.period_lattice_automultipliers_finite
