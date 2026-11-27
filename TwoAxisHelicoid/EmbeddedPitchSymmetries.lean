import TwoAxisHelicoid.EmbeddedPitchPhysicalRepresentative
import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The two ambient half-turns of the HWV symmetric class preserve the
actual spatial image of each proposed pitch-normalized representative. -/
theorem pitch_geometric_half_turns (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily)
    (s : OriginalHelicoidRepresentative) (e : s.image = W.image) :
    halfTurnX '' range s.position = range s.position ∧ halfTurnZ '' range s.position = range s.position := by
  let L := rhombicPeriodPair W.t W.ht
  let S := W.position '' (L.lattice : Set ℂ)ᶜ
  obtain ⟨h,_⟩ := hW
  have eq : range s.position = S := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.image_injective
    change coordinateToEuclidean '' range s.position = coordinateToEuclidean '' (W.position '' (L.lattice : Set ℂ)ᶜ)
    rw [← range_comp,image_image]
    exact e
  have hc {z : ℂ} (hz : z ∉ L.lattice) : conj z ∉ L.lattice :=
    fun hn => hz (by simpa only [conj_conj] using rhombic_conj_mem W.ht hn)
  have hx : MapsTo halfTurnX S S := by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨conj z,hc hz,h.conjugation z hz⟩
  have hv : MapsTo halfTurnZ S S := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨-conj z,fun hn => hc hz (by simpa using L.lattice.neg_mem hn),?_⟩
    rw [h.neg _ (hc hz),h.conjugation z hz]
    ext j
    fin_cases j <;> simp [halfTurnZ]
  have image_eq {R : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hr : Function.Involutive R) (hm : MapsTo R S S) :
      R '' S = S := Subset.antisymm hm.image_subset (fun v hv => ⟨R v,hm hv,hr v⟩)
  rw [eq]
  exact ⟨image_eq halfTurnX_involutive hx,image_eq halfTurnZ_involutive hv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pitch_geometric_half_turns
