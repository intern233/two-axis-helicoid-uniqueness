import TwoAxisHelicoid.FlatEndCompactification

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

theorem range_cappedOnePointMap {M : Type*} (A H : ℝ) (X : M → HelicoidTubeCoordinates) :
    range (cappedOnePointMap A H X) = insert (planeCapNorth H) (range (ambientPlaneCap A H ∘ X)) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    induction p using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe q => exact Or.inr ⟨q,rfl⟩
  · rintro (rfl | ⟨q,rfl⟩)
    · exact ⟨OnePoint.infty,rfl⟩
    · exact ⟨OnePoint.some q,rfl⟩

/-- The actual capped surface, including its arbitrary compact core,
coincides with a round sphere in a neighborhood of the added point. -/
theorem cappedOnePointMap_spherical_neighborhood {M : Type*} {X : M → HelicoidTubeCoordinates}
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hexact : ∀ y, R^2 < ambientRadiusSq y → (y ∈ range X ↔ y.1.2 = 0)) :
    ∃ U : Set HelicoidTubeCoordinates, IsOpen U ∧ planeCapNorth H ∈ U ∧
      range (cappedOnePointMap A H X) ∩ U = planeCapSphere H ∩ U := by
  have hA0 : 0 ≤ A := by linarith
  have hH0 : 0 < H := by linarith
  have hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0 :=
    fun y hy hR => (hexact y hR).mp hy
  obtain ⟨V,hVo,hVN,hV⟩ := smoothPlaneCap_spherical_neighborhood hA0 hH0
  let U : Set HelicoidTubeCoordinates := V ∩ {y | R < y.1.2}
  refine ⟨U,hVo.inter (isOpen_lt continuous_const (by fun_prop)),⟨hVN,by dsimp [planeCapNorth]; linarith⟩,?_⟩
  ext y
  constructor
  · rintro ⟨hy,hyU⟩
    refine ⟨?_,hyU⟩
    have hm : y ∈ insert (planeCapNorth H) (range (smoothPlaneCap A H)) ∩ V := by
      refine ⟨?_,hyU.1⟩
      rw [range_cappedOnePointMap] at hy
      rcases hy with rfl | ⟨q,rfl⟩
      · exact Or.inl rfl
      · by_cases hq : (X q).1.1^2+(X q).2^2 ≤ A
        · have he := ambientPlaneCap_fixes (H := H) hq
          have hh : R < (X q).1.2 := by simpa only [Function.comp_apply,he,mem_ofPred_eq] using hyU.2
          have hr : R^2 < ambientRadiusSq (X q) := by
            dsimp [ambientRadiusSq]
            nlinarith [sq_nonneg (X q).1.1,sq_nonneg (X q).2]
          have hz := hflat (X q) (mem_range_self q) hr
          linarith
        · have hz := (ambientPlaneCap_far_point hR hA1 hAR hH hflat (mem_range_self q)
            (lt_of_not_ge hq)).1
          exact Or.inr ⟨((X q).1.1,(X q).2),(ambientPlaneCap_of_flat hz).symm⟩
    rw [hV] at hm
    exact hm.1
  · rintro ⟨hy,hyU⟩
    refine ⟨?_,hyU⟩
    have hm : y ∈ planeCapSphere H ∩ V := ⟨hy,hyU.1⟩
    rw [← hV] at hm
    rcases hm.1 with rfl | ⟨p,rfl⟩
    · exact ⟨OnePoint.infty,rfl⟩
    · have hq : A < p.1^2+p.2^2 := by
        by_contra hn
        have he := smoothPlaneCap_of_le (H := H) (le_of_not_gt hn)
        have hh := hyU.2
        rw [he] at hh
        change R < 0 at hh
        linarith
      have hr : R^2 < ambientRadiusSq ((p.1,0),p.2) := by
        dsimp [ambientRadiusSq]
        nlinarith [sq_nonneg R]
      obtain ⟨q,hqX⟩ := (hexact ((p.1,0),p.2) hr).mpr rfl
      refine ⟨OnePoint.some q,?_⟩
      change ambientPlaneCap A H (X q) = smoothPlaneCap A H p
      rw [hqX]
      exact ambientPlaneCap_of_flat rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.cappedOnePointMap_spherical_neighborhood
