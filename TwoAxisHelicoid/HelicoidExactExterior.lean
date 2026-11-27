import TwoAxisHelicoid.HelicoidC1Straightening
import TwoAxisHelicoid.HelicoidSphereCap

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 1000000

/-- A compact parameter complement and a full exterior chart give exact
equality of the spatial images outside a compact ambient set. -/
theorem HasExactHelicoidEnd.exact_outside_compact {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasExactHelicoidEnd X) (hX : Continuous X) :
    ∃ K : Set HelicoidTubeCoordinates, IsCompact K ∧ ∀ y, y ∉ K →
      (y ∈ range X ↔ ∃ p : ℝ × ℝ, helicoidTubeMap ((0,p.1),p.2) = y) := by
  obtain ⟨S,hS,B,_hB,E,hgraph⟩ := hEnd
  let H : (ℝ × ℝ) → HelicoidTubeCoordinates := fun p => helicoidTubeMap ((0,p.1),p.2)
  have hH : Continuous H := helicoidTubeMap_contDiff.continuous.comp (by fun_prop)
  let K := X '' Sᶜ ∪ H '' (exteriorPlaneBase B)ᶜ
  refine ⟨K,(hS.image hX).union ((exteriorPlaneBase_complement_isCompact B).image hH),?_⟩
  intro y hy
  constructor
  · rintro ⟨q,rfl⟩
    have hq : q ∈ S := by
      by_contra hn
      exact hy (Or.inl ⟨q,hn,rfl⟩)
    exact ⟨(E ⟨q,hq⟩).1,(hgraph ⟨q,hq⟩).symm⟩
  · rintro ⟨p,hp⟩
    have hpb : p ∈ exteriorPlaneBase B := by
      by_contra hn
      exact hy (Or.inr ⟨p,hn,hp⟩)
    refine ⟨(E.symm ⟨p,hpb⟩).1,?_⟩
    rw [hgraph,E.apply_symm_apply]
    exact hp

/-- The compact difference is contained in an actual Euclidean ball.
Every larger spherical section is exactly the standard helicoid section. -/
theorem HasExactHelicoidEnd.spherical_sections {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasExactHelicoidEnd X) (hX : Continuous X) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      range X ∩ {y | ambientRadiusSq y = R^2} =
        (fun p : ℝ × ℝ => helicoidTubeMap ((0,p.1),p.2)) '' {p | p.1^2+p.2^2 = R^2} := by
  obtain ⟨K,hK,houtside⟩ := hEnd.exact_outside_compact hX
  obtain ⟨L,hL⟩ := (hK.image ambientRadiusSq_continuous).isBounded.exists_norm_le
  refine ⟨|L|+1,by positivity,?_⟩
  intro R hR
  have hRbig : L < R^2 := by
    have ha := le_abs_self L
    have hb := abs_nonneg L
    nlinarith [sq_nonneg (|L|)]
  have hout (y : HelicoidTubeCoordinates) (hy : ambientRadiusSq y = R^2) : y ∉ K := by
    intro hyK
    have hb := hL (ambientRadiusSq y) ⟨y,hyK,rfl⟩
    rw [Real.norm_eq_abs,hy,abs_of_nonneg (sq_nonneg R)] at hb
    exact hRbig.not_ge hb
  ext y
  constructor
  · rintro ⟨hyX,hyR⟩
    obtain ⟨p,hp⟩ := (houtside y (hout y hyR)).mp hyX
    refine ⟨p,?_,hp⟩
    change ambientRadiusSq y = R^2 at hyR
    rw [← hp,helicoidTubeMap_zero_radius] at hyR
    exact hyR
  · rintro ⟨p,hp,rfl⟩
    have hr : ambientRadiusSq (helicoidTubeMap ((0,p.1),p.2)) = R^2 := by
      rw [helicoidTubeMap_zero_radius]
      exact hp
    exact ⟨(houtside _ (hout _ hr)).mpr ⟨p,rfl⟩,hr⟩

/-- The spherical cap meets the entire spatial image precisely at its
boundary; in particular its open disk avoids the retained compact core. -/
theorem HasExactHelicoidEnd.spherical_caps_meet_only_boundary {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasExactHelicoidEnd X) (hX : Continuous X) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R → ∀ p ∈ euclideanParameterDisk R,
      (helicoidSphereCap R p ∈ range X ↔ p.1^2+p.2^2 = R^2) := by
  obtain ⟨R₀,hR₀,hsections⟩ := hEnd.spherical_sections hX
  refine ⟨R₀,hR₀,?_⟩
  intro R hR p hp
  constructor
  · intro hx
    have hm : helicoidSphereCap R p ∈ range X ∩ {y | ambientRadiusSq y = R^2} :=
      ⟨hx,helicoidSphereCap_radius hp⟩
    rw [hsections R hR] at hm
    obtain ⟨q,_hq,heq⟩ := hm
    exact (helicoidSphereCap_mem_helicoid_iff hp).mp ⟨q,heq⟩
  · intro hb
    have hm : helicoidSphereCap R p ∈
        (fun q : ℝ × ℝ => helicoidTubeMap ((0,q.1),q.2)) '' {q | q.1^2+q.2^2 = R^2} :=
      ⟨p,hb,(helicoidSphereCap_boundary hb).symm⟩
    rw [← hsections R hR] at hm
    exact hm.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasExactHelicoidEnd.exact_outside_compact
#print axioms TwoAxisHelicoid.HasExactHelicoidEnd.spherical_sections
