import TwoAxisHelicoid.HeightEndBounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem proper_restrict_of_bounded_preimages {S : Set ℂ} (hS : IsClosed S)
    {X : ℂ → Fin 3 → ℝ} (hX : ContinuousOn X S)
    (hb : ∀ B : ℝ, 0 ≤ B → ∃ D > (0 : ℝ), ∀ z ∈ S, ‖X z‖ ≤ B → ‖z‖ ≤ D) :
    IsProperMap (fun z : S => X z.1) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuousOn_iff_continuous_domRestrict.mp hX,?_⟩
  intro K hK
  obtain ⟨B,hB,hKB⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨D,_,hD⟩ := hb B hB.le
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' ((fun z : S => X z.1) ⁻¹' K) = S ∩ X ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨⟨w,hw⟩,hkw,rfl⟩
      exact ⟨hw,hkw⟩
    · rintro ⟨hz,hkz⟩
      exact ⟨⟨z,hz⟩,hkz,rfl⟩
  rw [he]
  apply (isCompact_closedBall (0 : ℂ) D).of_isClosed_subset
    (hX.preimage_isClosed_of_isClosed hS hK.isClosed)
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using hD z hz.1 (hKB _ hz.2)

/-- Height-normalized Weierstrass data with a vanishing helicoidal
correction give an actually proper spatial map on every closed subend.
No embeddedness, properness or extrinsic escape is assumed in this result. -/
theorem height_normalized_helicoidal_end_isProperMap
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (α b R₀ R : ℝ) (hR : R₀ < R)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re+b)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) :
    IsProperMap (fun z : {z : ℂ // R ≤ ‖z‖} => X z.1) := by
  obtain ⟨Y,hY,hRY,hsmall⟩ := helicoidal_correction_small_phase hF R₀
  apply proper_restrict_of_bounded_preimages (isClosed_le continuous_const continuous_norm)
    (fun z hz => (hX z (hR.trans_le hz)).continuousAt.continuousWithinAt)
  intro B hB
  obtain ⟨D,hD,hbound⟩ := height_end_bounded_image_parameter_bound α b R₀ Y hY.le hRY hX hheight hsmall hB
  exact ⟨D,hD,fun z hz => hbound z (hR.trans_le hz)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_normalized_helicoidal_end_isProperMap
