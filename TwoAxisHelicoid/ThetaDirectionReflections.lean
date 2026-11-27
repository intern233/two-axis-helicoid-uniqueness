import TwoAxisHelicoid.TorusThetaDirection
import TwoAxisHelicoid.RhombicCenteredRectangle

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaScaledJet

theorem torusThetaDirection_neg (t a : ℝ) (z : ℂ) :
    torusThetaDirection t a (-z)=(torusThetaDirection t a z)⁻¹ := by
  unfold torusThetaDirection
  rw [show -z-(a:ℂ)= -(z+a) by ring,show -z+(a:ℂ)= -(z-a) by ring,
    thetaScaledJet_neg,thetaScaledJet_neg]
  simp [Complex.exp_neg,mul_inv_rev,mul_comm]

theorem torusThetaDirection_conj (t a : ℝ) (z : ℂ) :
    torusThetaDirection t a (conj z)=conj (torusThetaDirection t a z) := by
  unfold torusThetaDirection
  simp only [map_mul,map_div₀,← exp_conj,conj_I,conj_ofReal,conj_im]
  rw [← thetaScaledJet_conj,← thetaScaledJet_conj]
  simp

theorem theta_direction_inverse_re_neg {z : ℂ} : z⁻¹.re<0 ↔ z.re<0 := by
  by_cases h : z=0
  · simp [h]
  · rw [inv_re,div_lt_iff₀ (normSq_pos.mpr h),zero_mul]

/-- The lattice and two reflections reduce an invariant condition on
the entire parameter plane to a single closed half of the basic rectangle. -/
theorem rhombic_reflection_half_rectangle {t : ℝ} (ht : 0<t) (P : ℂ → Prop)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → P z → P (z+ω))
    (turn : ∀ z, P z → P (-z)) (mirror : ∀ z, P z → P (-conj z))
    (rect : ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc 0 (t/2), P ((x:ℂ)+I*y)) : ∀ z, P z := by
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  have positive (x y : ℝ) (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc 0 t) : P (Z x y) := by
    by_cases below : y≤t/2
    · exact rect _ hx _ ⟨hy.1,below⟩
    have bound : 1-x∈Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hx.2,by linarith [hx.1]⟩
    have boundY : t-y∈Icc 0 (t/2) := ⟨sub_nonneg.mpr hy.2,by linarith⟩
    have m := per _ _ (rhombicPeriodPair t ht).ω₂_mem_lattice (turn _ (rect _ bound _ boundY))
    convert m using 1
    dsimp [Z,rhombicPeriodPair]
    push_cast
    ring
  intro z
  obtain ⟨x,y,hx,hy,mem⟩ := rhombic_centered_rectangle_rep ht z
  have py : y∈Icc 0 t := ⟨hy.1,hy.2.le⟩
  have r : P (Z x y) := by
    rcases le_or_gt 0 x with right|left
    · exact positive _ _ ⟨right,hx.2.le⟩ py
    · have h := mirror _ (positive (-x) y ⟨(neg_pos.mpr left).le,by linarith [hx.1]⟩ py)
      simpa [Z,add_comm] using h
  have e := per _ _ mem r
  rwa [show Z x y+(z-((x:ℂ)+I*y))=z by dsimp [Z]; ring] at e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torusThetaDirection_neg
#print axioms TwoAxisHelicoid.torusThetaDirection_conj
#print axioms TwoAxisHelicoid.rhombic_reflection_half_rectangle
