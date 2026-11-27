import TwoAxisHelicoid.NullVectorRegularity
import TwoAxisHelicoid.RhombicRegularPaths

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The actual coefficient symmetries induced by the two orthogonal axes,
together with the usual nullity and immersion regularity conditions. -/
structure TwoAxisNullDifferential (L : PeriodPair) (p : ℂ → Fin 3 → ℂ) : Prop where
  periodic : ∀ z ω, ω ∈ L.lattice → p (z+ω) = p z
  null : ∀ z ∉ L.lattice, ComplexNull (p z)
  regular : ∀ z ∉ L.lattice, p z ≠ 0
  neg : ∀ z ∉ L.lattice, p (-z) = ![p z 0,-p z 1,p z 2]
  conjugation : ∀ z ∉ L.lattice, p (conj z) = ![conj (p z 0),-conj (p z 1),-conj (p z 2)]

theorem TwoAxisNullDifferential.height_zero_not_two_torsion {L : PeriodPair}
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential L p)
    {z : ℂ} (hz : z ∉ L.lattice) (hzero : p z 2 = 0) : 2*z ∉ L.lattice := by
  intro htwo
  have he : p (-z) = p z := by
    have h := hp.periodic z (-(2*z)) (L.lattice.neg_mem htwo)
    have he : z+ -(2*z) = -z := by ring
    rwa [he] at h
  have h₁ := congrFun (hp.neg z hz) 1
  change p (-z) 1 = -p z 1 at h₁
  rw [he] at h₁
  have h1 : p z 1 = 0 := by linear_combination h₁/2
  have hnull := hp.null z hz
  change (p z 0)^2+(p z 1)^2+(p z 2)^2 = 0 at hnull
  rw [h1,hzero] at hnull
  have h0 : p z 0 = 0 := by
    have hs : p z 0*p z 0 = 0 := by simpa [pow_two] using hnull
    exact (mul_eq_zero.mp hs).elim id id
  apply hp.regular z hz
  funext j
  fin_cases j <;> simp [h0,h1,hzero]

theorem TwoAxisNullDifferential.height_zero_not_vertical_fixed {L : PeriodPair}
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential L p)
    {z : ℂ} (hz : z ∉ L.lattice) (hzero : p z 2 = 0) : conj z+z ∉ L.lattice := by
  intro hv
  have he : p (conj z) = p (-z) := by
    have h := hp.periodic (-z) (conj z+z) hv
    have he : -z+(conj z+z) = conj z := by ring
    rwa [he] at h
  rw [hp.conjugation z hz,hp.neg z hz] at he
  have h₀ := congrArg Complex.im (congrFun he 0)
  have h₁ := congrArg Complex.im (congrFun he 1)
  change (conj (p z 0)).im = (p z 0).im at h₀
  change (-conj (p z 1)).im = (-p z 1).im at h₁
  simp only [Complex.conj_im,Complex.neg_im,neg_neg] at h₀ h₁
  have hi0 : (p z 0).im = 0 := by linarith
  have hi1 : (p z 1).im = 0 := by linarith
  have heq := (complexNull_real_identities (hp.null z hz)).1
  rw [hi0,hi1,hzero] at heq
  have hpos := nullMetric_pos (hp.null z hz) (hp.regular z hz)
  simp only [Complex.zero_im,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] at heq
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.TwoAxisNullDifferential.height_zero_not_two_torsion
#print axioms TwoAxisHelicoid.TwoAxisNullDifferential.height_zero_not_vertical_fixed
