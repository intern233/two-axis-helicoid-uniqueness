import TwoAxisHelicoid.PlaneCapSeparation
import TwoAxisHelicoid.PlaneCapSphericalTail

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff
set_option maxHeartbeats 1000000

/-- A globally smooth formula which caps a planar exterior and is the
identity on a full cylinder containing the prescribed compact core. -/
noncomputable def ambientPlaneCap (A H : ℝ) (y : HelicoidTubeCoordinates) : HelicoidTubeCoordinates :=
  let q := y.1.1^2+y.2^2
  ((planeCapScale A H q*y.1.1,y.1.2+planeCapHeight A H q),planeCapScale A H q*y.2)

theorem ambientPlaneCap_contDiff (A H : ℝ) : ContDiff ℝ (∞ : WithTop ℕ∞) (ambientPlaneCap A H) := by
  unfold ambientPlaneCap planeCapScale planeCapHeight planeCapSwitch
  dsimp only
  fun_prop (disch := intros; positivity)

theorem ambientPlaneCap_fixes {A H : ℝ} {y : HelicoidTubeCoordinates}
    (hy : y.1.1^2+y.2^2 ≤ A) : ambientPlaneCap A H y = y := by
  simp [ambientPlaneCap,planeCapScale_of_le hy,planeCapHeight_of_le hy]

theorem ambientPlaneCap_of_flat {A H : ℝ} {y : HelicoidTubeCoordinates} (hy : y.1.2 = 0) :
    ambientPlaneCap A H y = smoothPlaneCap A H (y.1.1,y.2) := by
  simp [ambientPlaneCap,smoothPlaneCap,hy]

theorem ambientPlaneCap_fixes_ball {A H R : ℝ} (hA : R^2 ≤ A) {y : HelicoidTubeCoordinates}
    (hy : ambientRadiusSq y ≤ R^2) : ambientPlaneCap A H y = y := by
  apply ambientPlaneCap_fixes
  dsimp [ambientRadiusSq] at hy
  nlinarith [sq_nonneg y.1.2]

theorem ambientPlaneCap_far_point {A H R : ℝ} {S : Set HelicoidTubeCoordinates}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ S, R^2 < ambientRadiusSq y → y.1.2 = 0)
    {y : HelicoidTubeCoordinates} (hyS : y ∈ S) (hy : A < y.1.1^2+y.2^2) :
    y.1.2 = 0 ∧ R^2 < ambientRadiusSq (ambientPlaneCap A H y) ∧
      0 < (ambientPlaneCap A H y).1.2 := by
  have hf : y.1.2 = 0 := by
    apply hflat y hyS
    dsimp [ambientRadiusSq]
    nlinarith [sq_nonneg y.1.2,sq_nonneg R]
  refine ⟨hf,?_,?_⟩
  · rw [ambientPlaneCap_of_flat hf]
    exact smoothPlaneCap_outside_core hR hH (hA1.trans hy.le) (hAR.trans hy.le)
  · rw [ambientPlaneCap_of_flat hf]
    exact planeCapHeight_pos (by linarith) (by linarith) hy

/-- Capping preserves global embeddedness for an actual subset which is
planar outside the core ball. Injectivity is proved across the core and
the cap as well as within each piece. -/
theorem ambientPlaneCap_injOn_flat_exterior {A H R : ℝ} {S : Set HelicoidTubeCoordinates}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ S, R^2 < ambientRadiusSq y → y.1.2 = 0) :
    S.InjOn (ambientPlaneCap A H) := by
  intro x hxS y hyS he
  have hA0 : 0 ≤ A := by linarith
  have hH0 : 0 < H := by linarith
  by_cases hx : x.1.1^2+x.2^2 ≤ A
  · rw [ambientPlaneCap_fixes hx] at he
    by_cases hy : y.1.1^2+y.2^2 ≤ A
    · rwa [ambientPlaneCap_fixes hy] at he
    · obtain ⟨_hyflat,hyR,hypos⟩ := ambientPlaneCap_far_point hR hA1 hAR hH hflat hyS (lt_of_not_ge hy)
      rw [← he] at hyR hypos
      rw [hflat x hxS hyR] at hypos
      exact False.elim (lt_irrefl 0 hypos)
  · by_cases hy : y.1.1^2+y.2^2 ≤ A
    · rw [ambientPlaneCap_fixes hy] at he
      obtain ⟨_hxflat,hxR,hxpos⟩ := ambientPlaneCap_far_point hR hA1 hAR hH hflat hxS (lt_of_not_ge hx)
      rw [he] at hxR hxpos
      rw [hflat y hyS hxR] at hxpos
      exact False.elim (lt_irrefl 0 hxpos)
    · obtain ⟨hxflat,_hxR,_hxpos⟩ := ambientPlaneCap_far_point hR hA1 hAR hH hflat hxS (lt_of_not_ge hx)
      obtain ⟨hyflat,_hyR,_hypos⟩ := ambientPlaneCap_far_point hR hA1 hAR hH hflat hyS (lt_of_not_ge hy)
      rw [ambientPlaneCap_of_flat hxflat,ambientPlaneCap_of_flat hyflat] at he
      have hcoords := smoothPlaneCap_injective hA0 hH0 he
      have hxc := congrArg (fun p : ℝ × ℝ => p.1) hcoords
      have hzc := congrArg (fun p : ℝ × ℝ => p.2) hcoords
      exact Prod.ext (Prod.ext hxc (hxflat.trans hyflat.symm)) hzc

theorem ambientPlaneCap_avoids_north {A H R : ℝ} {S : Set HelicoidTubeCoordinates}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ S, R^2 < ambientRadiusSq y → y.1.2 = 0)
    {y : HelicoidTubeCoordinates} (hyS : y ∈ S) : ambientPlaneCap A H y ≠ planeCapNorth H := by
  have hH0 : 0 < H := by linarith
  intro he
  by_cases hy : y.1.1^2+y.2^2 ≤ A
  · rw [ambientPlaneCap_fixes hy] at he
    have hr : R^2 < ambientRadiusSq y := by
      rw [he]
      dsimp [ambientRadiusSq,planeCapNorth]
      nlinarith
    have hf := hflat y hyS hr
    rw [he] at hf
    exact hH0.ne' hf
  · have hf := (ambientPlaneCap_far_point hR hA1 hAR hH hflat hyS (lt_of_not_ge hy)).1
    rw [ambientPlaneCap_of_flat hf] at he
    have hh := congrArg (fun z : HelicoidTubeCoordinates => z.1.2) he
    have hb := planeCapHeight_lt (A := A) hH0 (add_nonneg (sq_nonneg y.1.1) (sq_nonneg y.2))
    exact hb.ne hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ambientPlaneCap_injOn_flat_exterior
#print axioms TwoAxisHelicoid.ambientPlaneCap_avoids_north
