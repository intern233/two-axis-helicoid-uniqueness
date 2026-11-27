import TwoAxisHelicoid.HelicoidGlobalTube
import TwoAxisHelicoid.OpenChartConjugation

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology

/-- The actual global helicoid tube, with the normal coordinate first
and the two base coordinates grouped together. -/
noncomputable def helicoidFiberChart :
    OpenPartialHomeomorph (ℝ × (ℝ × ℝ)) HelicoidTubeCoordinates where
  toFun := fun x => helicoidTubeMap ((x.1,x.2.1),x.2.2)
  invFun := fun y => ((helicoidGlobalTube.symm y).1.1,
    ((helicoidGlobalTube.symm y).1.2,(helicoidGlobalTube.symm y).2))
  source := {x | |x.1| < 1}
  target := helicoidGlobalTube.target
  map_source' x hx := helicoidGlobalTube.map_source hx
  map_target' y hy := helicoidGlobalTube.map_target hy
  left_inv' x hx := by
    change ((helicoidGlobalTube.symm (helicoidGlobalTube ((x.1,x.2.1),x.2.2))).1.1,
      ((helicoidGlobalTube.symm (helicoidGlobalTube ((x.1,x.2.1),x.2.2))).1.2,
        (helicoidGlobalTube.symm (helicoidGlobalTube ((x.1,x.2.1),x.2.2))).2)) = x
    rw [helicoidGlobalTube.left_inv hx]
  right_inv' y hy := helicoidGlobalTube.right_inv hy
  open_source := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  open_target := helicoidGlobalTube.open_target
  continuousOn_toFun := helicoidGlobalTube.continuousOn.comp
    (show Continuous (fun x : ℝ × (ℝ × ℝ) => ((x.1,x.2.1),x.2.2)) by fun_prop).continuousOn
      (fun _ h => h)
  continuousOn_invFun := helicoidGlobalTube.continuousOn_symm.fst.fst.prodMk
    (helicoidGlobalTube.continuousOn_symm.fst.snd.prodMk helicoidGlobalTube.continuousOn_symm.snd)

/-- Euclidean distance to the actual helicoid, expressed in the product
coordinate representation of ambient three-space. -/
noncomputable def ambientHelicoidDistance (y : HelicoidTubeCoordinates) : ℝ :=
  infDist (helicoidEuclideanPoint (y.1.1,y.1.2,y.2)) euclideanHelicoidSet

theorem ambientHelicoidDistance_continuous : Continuous ambientHelicoidDistance := by
  apply (continuous_infDist_pt euclideanHelicoidSet).comp
  change Continuous (fun y : HelicoidTubeCoordinates => !₂[y.1.1,y.1.2,y.2])
  fun_prop

theorem helicoidFiberChart_target_iff (y : HelicoidTubeCoordinates) :
    y ∈ helicoidFiberChart.target ↔ ambientHelicoidDistance y < 1 :=
  helicoidTubeEquiv_target_iff_distance

theorem helicoidFiberChart_distance {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidFiberChart.target) :
    |(helicoidFiberChart.symm y).1| = ambientHelicoidDistance y :=
  helicoidSignedDistance_abs_eq_infDist hy

theorem helicoidFiberChart_half_support_closed :
    IsClosed {y : HelicoidTubeCoordinates | ambientHelicoidDistance y ≤ 1/2} :=
  isClosed_le ambientHelicoidDistance_continuous continuous_const

theorem helicoidFiberChart_half_support_subset :
    {y : HelicoidTubeCoordinates | ambientHelicoidDistance y ≤ 1/2} ⊆ helicoidFiberChart.target := by
  intro y hy
  exact (helicoidFiberChart_target_iff y).mpr (hy.trans_lt (by norm_num))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidFiberChart
#print axioms TwoAxisHelicoid.helicoidFiberChart_half_support_subset
