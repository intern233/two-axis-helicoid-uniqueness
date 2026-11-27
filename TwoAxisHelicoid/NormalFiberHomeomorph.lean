import TwoAxisHelicoid.SmallFiberShift
import TwoAxisHelicoid.BoundedDisplacementProper
import Mathlib.Analysis.Normed.Group.Constructions

namespace TwoAxisHelicoid
open Set

/-- Quantitative data for an actual scalar cutoff. These estimates will
be supplied by a smooth bump function, rather than by a homeomorphism
assumption. -/
structure FiberCutoff (χ : ℝ → ℝ) (C R : ℝ) : Prop where
  differentiable : Differentiable ℝ χ
  derivative_bound : ∀ s, |deriv χ s| ≤ C
  value_bound : ∀ s, |χ s| ≤ 1
  radius_pos : 0 < R
  support_bound : ∀ s, R ≤ |s| → χ s = 0
  at_zero : χ 0 = 1

theorem FiberCutoff.constant_nonneg {χ : ℝ → ℝ} {C R : ℝ} (hχ : FiberCutoff χ C R) : 0 ≤ C :=
  (abs_nonneg _).trans (hχ.derivative_bound 0)

theorem FiberCutoff.small_coefficient {P : Type*} {χ : ℝ → ℝ} {C R U time : ℝ}
    (hχ : FiberCutoff χ C R) {u : P → ℝ} (hu : ∀ p, |u p| ≤ U)
    (hsmall : U*C < 1) (htime : time ∈ Icc (0 : ℝ) 1) (p : P) : |time*u p| *C < 1 :=
  scalarFiberShift_time_bound
    ((mul_le_mul_of_nonneg_right (hu p) hχ.constant_nonneg).trans_lt hsmall)
    hχ.constant_nonneg htime

noncomputable def normalFiberShift {P : Type*} (χ : ℝ → ℝ) (u : P → ℝ) (time : ℝ)
    (x : ℝ × P) : ℝ × P := (scalarFiberShift χ (time*u x.2) x.1,x.2)

theorem normalFiberShift_continuous {P : Type*} [TopologicalSpace P]
    {χ : ℝ → ℝ} {u : P → ℝ} (hχ : Continuous χ) (hu : Continuous u) (time : ℝ) :
    Continuous (normalFiberShift χ u time) := by
  unfold normalFiberShift scalarFiberShift
  fun_prop

theorem normalFiberShift_bijective {P : Type*} {χ : ℝ → ℝ} {C R U time : ℝ}
    (hχ : FiberCutoff χ C R) {u : P → ℝ} (hu : ∀ p, |u p| ≤ U)
    (hsmall : U*C < 1) (htime : time ∈ Icc (0 : ℝ) 1) :
    Function.Bijective (normalFiberShift χ u time) := by
  constructor
  · intro x y h
    have hp := congrArg Prod.snd h
    change x.2 = y.2 at hp
    have hs : scalarFiberShift χ (time*u x.2) x.1 = scalarFiberShift χ (time*u y.2) y.1 :=
      congrArg Prod.fst h
    rw [hp] at hs
    exact Prod.ext ((scalarFiberShift_strictMono hχ.differentiable hχ.derivative_bound
      (hχ.small_coefficient hu hsmall htime y.2)).injective hs) hp
  · rintro ⟨s,p⟩
    obtain ⟨r,hr⟩ := scalarFiberShift_surjective hχ.differentiable.continuous hχ.support_bound (time*u p) s
    exact ⟨(r,p),Prod.ext hr rfl⟩

theorem normalFiberShift_bounded_displacement {P : Type*} [NormedAddCommGroup P]
    {χ : ℝ → ℝ} {u : P → ℝ} {U time : ℝ}
    (hχ : ∀ s, |χ s| ≤ 1) (hu : ∀ p, |u p| ≤ U) (htime : time ∈ Icc (0 : ℝ) 1)
    (x : ℝ × P) : ‖x-normalFiberShift χ u time x‖ ≤ U := by
  have ht : |time*u x.2| ≤ U := by
    rw [abs_mul,abs_of_nonneg htime.1]
    exact (mul_le_mul_of_nonneg_right htime.2 (abs_nonneg _)).trans (by simpa using hu x.2)
  have hb : |χ x.1*(time*u x.2)| ≤ U := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hχ x.1) (abs_nonneg _)).trans (by simpa using ht)
  have he : x.1-scalarFiberShift χ (time*u x.2) x.1 = -(χ x.1*(time*u x.2)) := by
    unfold scalarFiberShift
    ring
  change max ‖x.1-scalarFiberShift χ (time*u x.2) x.1‖ ‖x.2-x.2‖ ≤ U
  rw [he,sub_self,norm_zero,norm_neg,Real.norm_eq_abs,
    max_eq_left (abs_nonneg (χ x.1*(time*u x.2)))]
  exact hb

theorem normalFiberShift_isProperMap {P : Type*} [NormedAddCommGroup P] [ProperSpace P]
    {χ : ℝ → ℝ} {u : P → ℝ} {U time : ℝ}
    (hχc : Continuous χ) (huc : Continuous u) (hχ : ∀ s, |χ s| ≤ 1)
    (hu : ∀ p, |u p| ≤ U) (htime : time ∈ Icc (0 : ℝ) 1) :
    IsProperMap (normalFiberShift χ u time) :=
  bounded_displacement_isProperMap (normalFiberShift_continuous hχc huc time)
    (normalFiberShift_bounded_displacement hχ hu htime)

/-- Every time slice is a genuine homeomorphism of the whole normal
coordinate space, with the exact fiber-shift formula. -/
noncomputable def normalFiberHomeomorph {P : Type*} [NormedAddCommGroup P] [ProperSpace P]
    {χ : ℝ → ℝ} {C R U time : ℝ} (hχ : FiberCutoff χ C R) {u : P → ℝ}
    (huc : Continuous u) (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1)
    (htime : time ∈ Icc (0 : ℝ) 1) : (ℝ × P) ≃ₜ (ℝ × P) :=
  (Equiv.ofBijective (normalFiberShift χ u time)
    (normalFiberShift_bijective hχ hu hsmall htime)).toHomeomorphOfContinuousClosed
      (normalFiberShift_continuous hχ.differentiable.continuous huc time)
      (normalFiberShift_isProperMap hχ.differentiable.continuous huc hχ.value_bound hu htime).isClosedMap

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalFiberHomeomorph
