import TwoAxisHelicoid.ProperUnitCurveTails

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

/-- Unit tangent curve segments on the actual surface, with acceleration
controlled outside one fixed compact core. Thinness is not included here. -/
def HasUnitTangentSegments {M : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : M → HelicoidTubeCoordinates) (D : M → E →L[ℝ] HelicoidTubeCoordinates)
    (K : Set M) (A : ℝ) : Prop :=
  ∀ q v, (∑ i, (tubeCartesian (D q v) i)^2) = 1 →
    ∃ γ : ℝ → M, ∃ w a : ℝ → HelicoidTubeCoordinates,
      γ 0 = q ∧ w 0 = D q v ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (X ∘ γ) (w t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (a t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (∑ i, (tubeCartesian (w t) i)^2) ≤ 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K → (∑ i, (tubeCartesian (a t) i)^2) ≤ A^2)

/-- Properness and thin tails turn actual unit tangent segments into the
controlled curves required by the C¹ normal-graph theorem. -/
theorem unit_tangent_segments_controlled_on_thin_tails
    {M : Type*} [TopologicalSpace M] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : M → HelicoidTubeCoordinates} (hp : IsProperMap X)
    {D : M → E →L[ℝ] HelicoidTubeCoordinates} {K₀ : Set M} (hK₀ : IsCompact K₀)
    {A : ℝ} (hseg : HasUnitTangentSegments X D K₀ A)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target ∧ |helicoidSignedDistance (X q)| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ L : Set M, IsCompact L ∧
      ∀ q ∉ L, HasControlledUnitTangentCurves (X q) (D q) ε A := by
  intro ε hε0 hε
  obtain ⟨K,hK,hKt⟩ := hthin ε hε0
  obtain ⟨L,hL,havoid⟩ := proper_surface_unit_curve_avoids_core hp (hK₀.union hK)
  refine ⟨L,hL,?_⟩
  intro q hq v hv
  obtain ⟨γ,w,a,hγ,hw,hxd,hwd,hspeed,hacc⟩ := hseg q v hv
  have hstay := havoid q hq γ w hγ hxd hspeed
  have hroot : sqrt ε ≤ 1 := by nlinarith [sq_sqrt hε0.le,sqrt_nonneg ε]
  have hsub : Icc (0 : ℝ) (sqrt ε) ⊆ Icc 0 1 :=
    fun _ ht => ⟨ht.1,ht.2.trans hroot⟩
  have hnot₀ t (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∉ K₀ := fun h => hstay t ht (Or.inl h)
  have hnot t (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∉ K := fun h => hstay t ht (Or.inr h)
  exact ⟨X ∘ γ,w,a,by simp only [Function.comp_apply,hγ],hw,
    fun t ht => hxd t (hsub ht),fun t ht => hwd t (hsub ht),
    fun t ht => (hKt (γ t) (hnot t (hsub ht))).1,
    fun t ht => (hKt (γ t) (hnot t (hsub ht))).2,
    fun t ht => hspeed t (hsub ht),fun t ht => hacc t (hsub ht) (hnot₀ t (hsub ht))⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unit_tangent_segments_controlled_on_thin_tails
