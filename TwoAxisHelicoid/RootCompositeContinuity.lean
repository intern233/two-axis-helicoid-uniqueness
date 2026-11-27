import TwoAxisHelicoid.ThetaCompositeContinuity
import TwoAxisHelicoid.RootDerivativeData
import TwoAxisHelicoid.RootHorizontalHalf

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaA thetaJet thetaQuotient

theorem root_horizontal_shift_regular {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) (a x : ℝ) :
    (x : ℂ)+I*((t/2 : ℝ) : ℂ)-(a : ℂ) ∈ thetaRegular t := by
  have he : ((x-a : ℝ) : ℂ)+I*((t/2 : ℝ) : ℂ) = (x : ℂ)+I*((t/2 : ℝ) : ℂ)-(a : ℂ) := by
    push_cast
    ring
  rw [← he]
  exact root_horizontal_regular htl htu (x-a)

theorem root_composite_continuousOn {α : Type*} [TopologicalSpace α] {S : Set α}
    {u b x : α → ℝ} (hu : ContinuousOn u S) (hb : ContinuousOn b S) (hx : ContinuousOn x S)
    (ht : ∀ p ∈ S, u p ∈ Icc (rootTLower : ℝ) rootTUpper)
    (ha : ∀ p ∈ S, b p ∈ Icc (rootALower : ℝ) rootAUpper) :
    ContinuousOn (fun p => thetaA (u p) (b p) ((x p : ℂ)+I*((u p/2 : ℝ) : ℂ))) S ∧
    ContinuousOn (fun p => thetaAa (u p) (b p) ((x p : ℂ)+I*((u p/2 : ℝ) : ℂ))) S ∧
    ContinuousOn (fun p => thetaAtMidline (u p) (b p) ((x p : ℂ)+I*((u p/2 : ℝ) : ℂ))) S := by
  let z : α → ℂ := fun p => (x p : ℂ)+I*((u p/2 : ℝ) : ℂ)
  have hz : ContinuousOn z S :=
    (Complex.continuous_ofReal.comp_continuousOn hx).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hu.div_const 2)))
  have htpos (p) (hp : p ∈ S) : 0 < u p :=
    lt_of_lt_of_le (by norm_num [rootTLower]) (ht p hp).1
  have he (p) (hp : p ∈ S) := rootDerivativeParameters.sound rootDerivativeParameters_valid
    (ht p hp).1 (ht p hp).2 (ha p hp).1 (ha p hp).2
  have hna (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*b p/2) ≠ 0 := (he p hp).abscissa_ne
  have hnv (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*z p/2) ≠ 0 :=
    root_horizontal_regular (ht p hp).1 (ht p hp).2 (x p)
  have hnm (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*(z p-b p)/2) ≠ 0 :=
    root_horizontal_shift_regular (ht p hp).1 (ht p hp).2 (b p) (x p)
  exact ⟨thetaA_comp_continuousOn hu hb hz htpos hna hnv,
    thetaAa_comp_continuousOn hu hb hz htpos hna hnv hnm,
    thetaAtMidline_comp_continuousOn hu hb hz htpos hna hnv hnm (fun p hp => (he p hp).zero_ne)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_composite_continuousOn
