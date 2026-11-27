import TwoAxisHelicoid.BoundedCoreHeightDegeneration
import TwoAxisHelicoid.ActualGlobalEndLength

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- Two actual lifted C¹ loops of a marked torus. Their combined deck
displacements generate the full lattice and their images on the given
spatial surface have a common bound for the ordinary Euclidean lengths. -/
structure BoundedGeneratingCore (L : PeriodPair) (X : ℂ → Fin 3 → ℝ) (B : ℝ) where
  arc : Fin 2 → ComplexPeriodArc (L.lattice : Set ℂ)ᶜ
  closed : ∀ i, (arc i).curve (arc i).right-(arc i).curve (arc i).left ∈ L.lattice
  generate : ∀ ω ∈ L.lattice, ∃ m n : ℤ,
    ω = (m:ℂ)*((arc 0).curve (arc 0).right-(arc 0).curve (arc 0).left)
      +(n:ℂ)*((arc 1).curve (arc 1).right-(arc 1).curve (arc 1).left)
  length_bound : ∀ i, (let a := arc i; Manifold.pathELength 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
    (coordinateToEuclidean ∘ X ∘ a.curve) a.left a.right) ≤ ENNReal.ofReal B

/-- Two bounded generating loops of the actual surface supply a nonzero
handle flux bounded by their lengths, with no choice of basis in advance. -/
theorem bounded_generating_core_nonzero_flux {t a c B : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (hG : thetaG t a = 0) (hB : 0 ≤ B)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (C : BoundedGeneratingCore (rhombicPeriodPair t ht) X B) :
    ∃ v ∈ range (heightBasisFlux t ht c), v ≠ 0 ∧ |v| ≤ B := by
  let L := rhombicPeriodPair t ht
  let ω := fun i => (C.arc i).curve (C.arc i).right-(C.arc i).curve (C.arc i).left
  have hor : (ω 0).re ≠ 0 ∨ (ω 1).re ≠ 0 := generating_deck_displacements_nonvertical L C.generate
  obtain ⟨i,hi⟩ : ∃ i, (ω i).re ≠ 0 := hor.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
  let b := C.arc i
  let f := fun z => coordinateData t a c ht z 2
  let v := (b.integral f).im
  have hf : ContinuousOn f (L.lattice : Set ℂ)ᶜ := fun z hz =>
    (((ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (coordinateData_analyticAt ht hz)).continuousAt.continuousWithinAt
  have he : v = -(Real.pi*c/t)*(ω i).re := piecewise_height_integral_im_deck ht ha hG
    (b.stays ⟨le_rfl,b.ordered⟩) (.arc b) (C.closed i)
  refine ⟨v,?_,he ▸ mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero hc) ht.ne')) hi,?_⟩
  · obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp (C.closed i)
    refine ⟨(m,n),?_⟩
    rw [heightBasisFlux_eq,he]
    change _ = -(Real.pi*c/t)*((C.arc i).curve (C.arc i).right-(C.arc i).curve (C.arc i).left).re
    rw [← hmn]
    simp [rhombicPeriodPair,Complex.mul_re]
    ring
  · have hlen := (b.height_flux_le_spatial_length (fun z hz => coordinateData_null ht ha hz) hf hX).trans (C.length_bound i)
    change ‖v‖ₑ ≤ ENNReal.ofReal B at hlen
    rw [← ofReal_norm,Real.norm_eq_abs] at hlen
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp hlen

/-- Normalized conformal surfaces with two uniformly bounded smooth
generating loops cannot approach the small-height degeneration. -/
theorem bounded_generating_cores_preclude_height_collapse {t c : ℕ → ℝ}
    (ht : ∀ n, 0 < t n) (hT : ∀ n, t n < ellipticVerticalUpper)
    (hc : ∀ n, |c n| = 2*(1-verticalA (t n))) {X : ℕ → ℂ → Fin 3 → ℝ}
    (hX : ∀ n, HasTwoAxisHelicoidCoordinateDifferential (X n) (t n) (verticalA (t n)) (c n) (ht n))
    {B : ℝ} (hB : 0 ≤ B) (C : ∀ n, BoundedGeneratingCore (rhombicPeriodPair (t n) (ht n)) (X n) B) :
    ¬ Tendsto t atTop (𝓝[>] 0) := by
  intro hlim
  have h (n : ℕ) : ∃ v ∈ range (heightBasisFlux (t n) (ht n) (c n)), v ≠ 0 ∧ |v| ≤ B := by
    obtain ⟨ha,hG⟩ := verticalA_spec ⟨ht n,hT n⟩
    have hn : c n ≠ 0 := by intro he; have := hc n; rw [he,abs_zero] at this; linarith [ha.2]
    exact bounded_generating_core_nonzero_flux (ht n) ha hn hG hB (hX n) (C n)
  choose v hv hn hb using h
  exact normalized_height_nonzero_flux_precludes_bounded_sequence hlim ht hc B hb hn hv

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_generating_cores_preclude_height_collapse
