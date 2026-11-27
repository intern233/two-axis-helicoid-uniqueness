import TwoAxisHelicoid.HelicoidNearestPoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace TwoAxisHelicoid
open Real Set Metric

abbrev HelicoidEuclideanSpace := EuclideanSpace ℝ (Fin 3)

noncomputable def helicoidEuclideanPoint (p : ℝ × ℝ × ℝ) : HelicoidEuclideanSpace :=
  !₂[p.1,p.2.1,p.2.2]

noncomputable def euclideanHelicoid (r θ : ℝ) : HelicoidEuclideanSpace :=
  !₂[r*cos θ,r*sin θ,θ]

noncomputable def euclideanHelicoidNormalMap (r θ s : ℝ) : HelicoidEuclideanSpace :=
  helicoidEuclideanPoint (helicoidNormalMap r θ s)

def euclideanHelicoidSet : Set HelicoidEuclideanSpace :=
  {p | ∃ r θ : ℝ, euclideanHelicoid r θ = p}

theorem helicoidEuclideanPoint_coordinates (p : HelicoidEuclideanSpace) :
    helicoidEuclideanPoint (p 0,p 1,p 2) = p := by
  ext i
  fin_cases i <;> rfl

theorem helicoidSquaredDistance_eq_euclidean_dist (p : ℝ × ℝ × ℝ) (r θ : ℝ) :
    helicoidSquaredDistance p r θ = dist (helicoidEuclideanPoint p) (euclideanHelicoid r θ)^2 := by
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
  simp [helicoidSquaredDistance,helicoidEuclideanPoint,euclideanHelicoid,Fin.sum_univ_succ,add_assoc]

theorem euclideanHelicoid_exists_nearest (p : HelicoidEuclideanSpace) :
    ∃ r θ : ℝ, ∀ u φ : ℝ,
      dist p (euclideanHelicoid r θ) ≤ dist p (euclideanHelicoid u φ) := by
  obtain ⟨r,θ,hmin⟩ := helicoidSquaredDistance_exists_min (p 0,p 1,p 2)
  refine ⟨r,θ,fun u φ => ?_⟩
  have h := hmin u φ
  simp only [helicoidSquaredDistance_eq_euclidean_dist,helicoidEuclideanPoint_coordinates] at h
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp h

theorem euclideanHelicoidSet_isClosed : IsClosed euclideanHelicoidSet := by
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨r,θ,hmin⟩ := euclideanHelicoid_exists_nearest p
  have hzero : dist p (euclideanHelicoid r θ) = 0 := by
    apply le_antisymm _ dist_nonneg
    by_contra hn
    have hd : 0 < dist p (euclideanHelicoid r θ) := lt_of_not_ge hn
    obtain ⟨q,hq,hpq⟩ := Metric.mem_closure_iff.mp hp _ hd
    obtain ⟨u,φ,rfl⟩ := hq
    exact (hmin u φ).not_gt hpq
  exact ⟨r,θ,(dist_eq_zero.mp hzero).symm⟩

theorem euclideanHelicoidNormalMap_distance (r θ s : ℝ) :
    dist (euclideanHelicoidNormalMap r θ s) (euclideanHelicoid r θ) = |s| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg s)).mp
  unfold euclideanHelicoidNormalMap
  rw [sq_abs,← helicoidSquaredDistance_eq_euclidean_dist]
  exact helicoidNormalMap_squaredDistance r θ s

theorem euclideanHelicoidNormalMap_infDist {r θ s : ℝ} (hs : |s| < 1) :
    infDist (euclideanHelicoidNormalMap r θ s) euclideanHelicoidSet = |s| := by
  apply le_antisymm
  · exact (infDist_le_dist_of_mem (show euclideanHelicoid r θ ∈ euclideanHelicoidSet from
      ⟨r,θ,rfl⟩)).trans_eq (euclideanHelicoidNormalMap_distance r θ s)
  · apply (le_infDist (show euclideanHelicoidSet.Nonempty from ⟨euclideanHelicoid 0 0,0,0,rfl⟩)).mpr
    intro p hp
    obtain ⟨u,φ,rfl⟩ := hp
    apply (sq_le_sq₀ (abs_nonneg s) dist_nonneg).mp
    unfold euclideanHelicoidNormalMap
    rw [sq_abs,← helicoidSquaredDistance_eq_euclidean_dist]
    exact helicoidNormalMap_nearest hs u φ

/-- The normal tube is exactly the ordinary Euclidean distance tube. -/
theorem euclideanHelicoid_distance_lt_one_iff (p : HelicoidEuclideanSpace) :
    infDist p euclideanHelicoidSet < 1 ↔
      ∃ r θ s : ℝ, |s| < 1 ∧ euclideanHelicoidNormalMap r θ s = p := by
  constructor
  · intro hp
    obtain ⟨r,θ,hmin⟩ := helicoidSquaredDistance_exists_min (p 0,p 1,p 2)
    obtain ⟨s,he,hd⟩ := helicoidSquaredDistance_min_is_normal hmin
    have hpoint : euclideanHelicoidNormalMap r θ s = p := by
      unfold euclideanHelicoidNormalMap
      rw [← he,helicoidEuclideanPoint_coordinates]
    have hdist : dist p (euclideanHelicoid r θ) = infDist p euclideanHelicoidSet := by
      apply le_antisymm
      · apply (le_infDist (show euclideanHelicoidSet.Nonempty from ⟨euclideanHelicoid 0 0,0,0,rfl⟩)).mpr
        intro q hq
        obtain ⟨u,φ,rfl⟩ := hq
        apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
        simpa only [helicoidSquaredDistance_eq_euclidean_dist,helicoidEuclideanPoint_coordinates]
          using hmin u φ
      · exact infDist_le_dist_of_mem ⟨r,θ,rfl⟩
    refine ⟨r,θ,s,?_,hpoint⟩
    rw [← hdist,← hpoint,euclideanHelicoidNormalMap_distance] at hp
    exact hp
  · rintro ⟨r,θ,s,hs,rfl⟩
    rw [euclideanHelicoidNormalMap_infDist hs]
    exact hs

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.euclideanHelicoidSet_isClosed
#print axioms TwoAxisHelicoid.euclideanHelicoid_distance_lt_one_iff
