import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

noncomputable def rhombicPeriodPair (t : ℝ) (ht : 0 < t) : PeriodPair where
  ω₁ := 2
  ω₂ := 1+I*t
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro a b h
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] at hi hr
    have hb : b = 0 := hi.resolve_right ht.ne'
    refine ⟨?_,hb⟩
    rw [hb] at hr
    linarith

theorem rhombic_conj_mem {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ (rhombicPeriodPair t ht).lattice) : conj z ∈ (rhombicPeriodPair t ht).lattice := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hz
  apply PeriodPair.mem_lattice.mpr
  refine ⟨m+n,-n,?_⟩
  rw [← he]
  simp only [rhombicPeriodPair, map_add, map_mul, map_intCast, map_one,
    map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

noncomputable def rhombicConjEquiv (t : ℝ) (ht : 0 < t) :
    (rhombicPeriodPair t ht).lattice ≃ (rhombicPeriodPair t ht).lattice where
  toFun z := ⟨conj (z : ℂ),rhombic_conj_mem ht z.property⟩
  invFun z := ⟨conj (z : ℂ),rhombic_conj_mem ht z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

theorem rhombic_weierstrassP_conj {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (rhombicPeriodPair t ht).weierstrassP (conj z) =
      conj ((rhombicPeriodPair t ht).weierstrassP z) := by
  unfold PeriodPair.weierstrassP
  rw [Complex.conj_tsum]
  rw [← (rhombicConjEquiv t ht).tsum_eq]
  apply tsum_congr
  intro l
  simp only [rhombicConjEquiv, map_sub, map_div₀, map_one, map_pow]
  rfl

theorem rhombic_weierstrassP_real {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ((rhombicPeriodPair t ht).weierstrassP (x : ℂ)).im = 0 := by
  have h := congrArg Complex.im (rhombic_weierstrassP_conj ht (x : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_conj
