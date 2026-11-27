import TwoAxisHelicoid.IntegerHeightEndCoordinate
import TwoAxisHelicoid.ActualEmbeddedEnd
import TwoAxisHelicoid.HeightEndEscape

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- Proper escape and an embedded height subend for all integer branches
are consequences of the actual differential. -/
theorem integer_primitive_end_escape_and_embedding
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ} (m : ℤ)
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      HasFDerivAt X (nullRealDerivative
        (weierstrassTriple (thetaGauss t a m z) (coordinateData t a c ht z 2))) z) :
    Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ)) ∧
      ∃ (K : ℂ → ℂ) (R : ℝ),
        Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧
        (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
        (∀ ξ : ℂ, R ≤ ‖ξ‖ → actualComplexHeight t a c ht (K ξ) = ξ) ∧
        IsClosedEmbedding (fun ξ : {ξ : ℂ // R ≤ ‖ξ‖} => X (K ξ.1)) := by
  obtain ⟨K,f,b,R₀,hK,hf,hf0,hKL,hcoord⟩ := integer_primitive_analytic_height_end_coordinate m ht ha hc hX
  have hF := infinityCorrection_tendsto_zero hf hf0
  have hY := height_normalized_helicoidal_end_tendsto (2*(a-m)/c) b R₀
    (fun z hz => (hcoord z hz).2.1) (fun z hz => (hcoord z hz).2.2) hF
  have hcomp := hY.comp (actualComplexHeight_tendsto (a := a) ht hc)
  have hrot : Tendsto (fun z => verticalRotation I (X z)) (𝓝[≠] (0 : ℂ))
      (cobounded (Fin 3 → ℝ)) := by
    apply hcomp.congr'
    filter_upwards [hKL] with z hz
    simp only [Function.comp_def,hz]
  have hescape : Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ)) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [Function.comp_def,vertical_quarter_turn_norm] using
      (tendsto_norm_atTop_iff_cobounded.mpr hrot)
  obtain ⟨R,hR,hEmb⟩ := height_normalized_helicoidal_end_eventually_embedded
    (2*(a-m)/c) b R₀ (fun z hz => (hcoord z hz).2.1) (fun z hz => (hcoord z hz).2.2) hF
  exact ⟨hescape,K,R,hK,hKL,(fun ξ hξ => (hcoord ξ (hR.trans_le hξ)).1),
    (vertical_quarter_turn_embedding_iff _).mp hEmb⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integer_primitive_end_escape_and_embedding
