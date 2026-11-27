import TwoAxisHelicoid.HelicoidExactExterior

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

theorem helicoidTubeRotation_symm_radius (y : HelicoidTubeCoordinates) :
    ambientRadiusSq (helicoidTubeRotation.symm y) = ambientRadiusSq y := by
  simpa only [Homeomorph.apply_symm_apply] using
    (helicoidTubeRotation_radius (helicoidTubeRotation.symm y)).symm

/-- The explicit ambient untwisting is a smooth diffeomorphism preserving
actual Euclidean spheres. An exact helicoidal end becomes precisely the
whole plane outside a sufficiently large ball, in both directions. -/
theorem HasExactHelicoidEnd.untwisted_plane_exterior {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasExactHelicoidEnd X) (hX : Continuous X) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ y : HelicoidTubeCoordinates,
      R^2 < ambientRadiusSq y →
      (y ∈ range (helicoidTubeRotation.symm ∘ X) ↔ y.1.2 = 0) := by
  obtain ⟨K,hK,houtside⟩ := hEnd.exact_outside_compact hX
  obtain ⟨L,hL⟩ := (hK.image ambientRadiusSq_continuous).isBounded.exists_norm_le
  refine ⟨|L|+1,by positivity,?_⟩
  intro R hR y hy
  have hRbig : L < R^2 := by
    nlinarith [le_abs_self L,abs_nonneg L,sq_nonneg (|L|)]
  have hout : helicoidTubeRotation y ∉ K := by
    intro hyK
    have hb := hL _ ⟨helicoidTubeRotation y,hyK,rfl⟩
    rw [Real.norm_eq_abs,helicoidTubeRotation_radius] at hb
    have hn := le_abs_self (ambientRadiusSq y)
    linarith
  constructor
  · rintro ⟨q,hq⟩
    have hx : helicoidTubeRotation y ∈ range X := by
      refine ⟨q,?_⟩
      rw [← hq]
      exact (helicoidTubeRotation.apply_symm_apply (X q)).symm
    obtain ⟨p,hp⟩ := (houtside _ hout).mp hx
    rw [helicoidTubeMap_zero_eq_rotation] at hp
    have he := helicoidTubeRotation.injective hp
    exact (congrArg (fun z : HelicoidTubeCoordinates => z.1.2) he).symm
  · intro hy0
    have hh : ∃ p : ℝ × ℝ, helicoidTubeMap ((0,p.1),p.2) = helicoidTubeRotation y := by
      refine ⟨(y.1.1,y.2),?_⟩
      rw [helicoidTubeMap_zero_eq_rotation]
      congr 1
      exact Prod.ext (Prod.ext rfl hy0.symm) rfl
    obtain ⟨q,hq⟩ := (houtside _ hout).mpr hh
    refine ⟨q,?_⟩
    change helicoidTubeRotation.symm (X q) = y
    rw [hq,helicoidTubeRotation.symm_apply_apply]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasExactHelicoidEnd.untwisted_plane_exterior
