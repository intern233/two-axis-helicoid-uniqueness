import TwoAxisHelicoid.ReferenceFrameHarmonic
import TwoAxisHelicoid.CoordinateSignMaps
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- A nonzero signed spatial dilation scales the height form by a
constant and leaves the actual Gauss quotient unchanged. -/
theorem scalar_dilation_end_orders {X : ℂ → Fin 3 → ℝ} {k : ℝ} (hk : k≠0)
    (regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ X z) :
    let Y := fun w => k • X w
    meromorphicOrderAt (fun w => immersionComplexCoefficient Y w 2) 0=
      meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) 0 ∧
    meromorphicOrderAt (immersionGaussLogDerivative Y) 0=meromorphicOrderAt (immersionGaussLogDerivative X) 0 := by
  let Y := fun w => k • X w
  have kn : (k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hk
  have co : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ j, immersionComplexCoefficient Y z j=(k:ℂ)*immersionComplexCoefficient X z j :=
    regular.mono fun z hz j => scalarComplexCoefficient_const_mul ((differentiableAt_pi.mp hz) j) k
  have ga : immersionGaussMap Y =ᶠ[𝓝[≠] (0:ℂ)] immersionGaussMap X := by
    filter_upwards [co] with z he
    unfold immersionGaussMap nullGauss nullHorizontalMinus
    rw [he,he,he,show (k:ℂ)*immersionComplexCoefficient X z 0-I*((k:ℂ)*immersionComplexCoefficient X z 1)=
      (k:ℂ)*(immersionComplexCoefficient X z 0-I*immersionComplexCoefficient X z 1) by ring,mul_div_mul_left _ _ kn]
  have ord := meromorphicOrderAt_congr (co.mono fun _ h => h 2)
  exact ⟨ord.trans (meromorphicOrderAt_const_smul_eq_meromorphicOrderAt kn),meromorphicOrderAt_congr (logDeriv_congr_nhdsNE ga)⟩

/-- In particular both poles are calculated in the original spatial
frame, before a possibly negative pitch normalization. -/
theorem reference_frame_end_orders {X : ℂ → Fin 3 → ℝ} {α : ℝ} (ha : α≠0)
    (regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ X z) :
    let Y := axisSpatialNormalization ha ![0,0,0] ∘ X
    meromorphicOrderAt (fun w => immersionComplexCoefficient Y w 2) 0=
      meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) 0 ∧
    meromorphicOrderAt (immersionGaussLogDerivative Y) 0=meromorphicOrderAt (immersionGaussLogDerivative X) 0 := by
  let R := lineAxisCoordinates (-1) (by simp) 0
  have reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ (R ∘ X) z := by
    filter_upwards [regular] with z hz
    exact (verticalRotation _).differentiableAt.comp z (hz.sub_const 0)
  obtain ⟨hh,hg⟩ := scalar_dilation_end_orders ha reg
  obtain ⟨oh,og⟩ := lineAxisCoordinates_end_orders (-1) (by simp) 0 regular
  have eq : axisSpatialNormalization ha ![0,0,0] ∘ X=(fun w => α • (R ∘ X) w) := funext fun w => reference_frame_scaled_rotation ha _
  dsimp only
  rw [eq]
  exact ⟨hh.trans oh,hg.trans og⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.reference_frame_end_orders
