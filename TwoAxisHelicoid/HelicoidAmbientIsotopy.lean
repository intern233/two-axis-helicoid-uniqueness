import TwoAxisHelicoid.HelicoidFiberChart
import TwoAxisHelicoid.NormalFiberIsotopy
import TwoAxisHelicoid.SupportedPartialHomeomorph

namespace TwoAxisHelicoid
open Set
open scoped Topology
set_option maxHeartbeats 1000000

variable {χ : ℝ → ℝ} {C U : ℝ} (hχ : FiberCutoff χ C (1/2))
  {u : ℝ × ℝ → ℝ} (huc : Continuous u) (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1)

theorem normalFiberHomeomorph_helicoid_source {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (x : ℝ × (ℝ × ℝ)) :
    x ∈ helicoidFiberChart.source ↔ normalFiberHomeomorph hχ huc hu hsmall htime x ∈ helicoidFiberChart.source := by
  change |x.1| < 1 ↔ |scalarFiberShift χ (time*u x.2) x.1| < 1
  exact (scalarFiberShift_preserves_strip hχ.differentiable (by norm_num) hχ.derivative_bound
    (hχ.small_coefficient hu hsmall htime x.2)
    (fun s hs => hχ.support_bound s ((by norm_num : (1/2 : ℝ) ≤ 1).trans hs)) x.1).symm

noncomputable def helicoidAmbientPartial {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    OpenPartialHomeomorph HelicoidTubeCoordinates HelicoidTubeCoordinates :=
  conjugateChartHomeomorph helicoidFiberChart (normalFiberHomeomorph hχ huc hu hsmall htime)
    (normalFiberHomeomorph_helicoid_source hχ huc hu hsmall htime)

theorem helicoidAmbientPartial_fixes {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {y : HelicoidTubeCoordinates} (hy : y ∈ helicoidFiberChart.target)
    (hn : y ∉ {y : HelicoidTubeCoordinates | ambientHelicoidDistance y ≤ 1/2}) :
    helicoidAmbientPartial hχ huc hu hsmall htime y = y := by
  apply conjugateChartHomeomorph_fixes helicoidFiberChart _ _ hy
  apply normalFiberHomeomorph_outside
  rw [helicoidFiberChart_distance hy]
  exact (lt_of_not_ge hn).le

/-- The actual ambient homeomorphism of three-space, equal to the
identity outside the half-width helicoid distance tube. -/
noncomputable def helicoidAmbientIsotopy {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates :=
  extendSupportedHomeomorph (helicoidAmbientPartial hχ huc hu hsmall htime) rfl
    helicoidFiberChart_half_support_closed helicoidFiberChart_half_support_subset
    (fun _ hy hn => helicoidAmbientPartial_fixes hχ huc hu hsmall htime hy hn)

theorem helicoidAmbientIsotopy_apply_in_tube {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {y : HelicoidTubeCoordinates} (hy : y ∈ helicoidFiberChart.target) :
    helicoidAmbientIsotopy hχ huc hu hsmall htime y =
      helicoidFiberChart (normalFiberHomeomorph hχ huc hu hsmall htime (helicoidFiberChart.symm y)) :=
  extendPartialMap_of_mem _ hy

theorem helicoidAmbientIsotopy_fixes_outside {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {y : HelicoidTubeCoordinates} (hn : 1/2 < ambientHelicoidDistance y) :
    helicoidAmbientIsotopy hχ huc hu hsmall htime y = y :=
  extendPartialMap_fixes _
    (fun _ hy hn => helicoidAmbientPartial_fixes hχ huc hu hsmall htime hy hn) (not_le.mpr hn)

theorem helicoidAmbientIsotopy_on_normal {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ helicoidFiberChart.source) :
    helicoidAmbientIsotopy hχ huc hu hsmall htime (helicoidFiberChart x) =
      helicoidFiberChart (normalFiberHomeomorph hχ huc hu hsmall htime x) := by
  rw [helicoidAmbientIsotopy_apply_in_tube hχ huc hu hsmall htime (helicoidFiberChart.map_source hx),
    helicoidFiberChart.left_inv hx]

theorem helicoidAmbientIsotopy_time_one_graph (p : ℝ × ℝ) :
    helicoidAmbientIsotopy hχ huc hu hsmall (by norm_num : (1 : ℝ) ∈ Icc 0 1)
        (helicoidTubeMap ((0,p.1),p.2)) = helicoidTubeMap ((u p,p.1),p.2) := by
  change helicoidAmbientIsotopy hχ huc hu hsmall _ (helicoidFiberChart (0,p)) = helicoidFiberChart (u p,p)
  rw [helicoidAmbientIsotopy_on_normal hχ huc hu hsmall _ (show (0,p) ∈ helicoidFiberChart.source from
      (by change |(0 : ℝ)| < 1; norm_num)),
    normalFiberHomeomorph_time_one_graph]

theorem helicoidAmbientIsotopy_time_zero :
    helicoidAmbientIsotopy hχ huc hu hsmall (by norm_num : (0 : ℝ) ∈ Icc 0 1) =
      Homeomorph.refl HelicoidTubeCoordinates := by
  apply Homeomorph.ext
  intro y
  by_cases hy : y ∈ helicoidFiberChart.target
  · rw [helicoidAmbientIsotopy_apply_in_tube hχ huc hu hsmall _ hy,
      normalFiberHomeomorph_time_zero]
    change helicoidFiberChart (helicoidFiberChart.symm y) = y
    exact helicoidFiberChart.right_inv hy
  · exact extendPartialMap_of_not_mem _ hy

theorem helicoidAmbientIsotopy_joint_continuous :
    Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates =>
      helicoidAmbientIsotopy hχ huc hu hsmall q.1.2 q.2) := by
  apply extendPartialMap_family_continuous
    (e := fun time : Icc (0 : ℝ) 1 => helicoidAmbientPartial hχ huc hu hsmall time.2)
    helicoidFiberChart.open_target helicoidFiberChart_half_support_closed
    helicoidFiberChart_half_support_subset (fun _ => rfl)
    (fun time _ hy hn => helicoidAmbientPartial_fixes hχ huc hu hsmall time.2 hy hn)
  have hcoords : ContinuousOn (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates =>
      (q.1,helicoidFiberChart.symm q.2)) (univ ×ˢ helicoidFiberChart.target) :=
    continuous_fst.continuousOn.prodMk
      (helicoidFiberChart.continuousOn_symm.comp continuous_snd.continuousOn (fun _ h => h.2))
  exact helicoidFiberChart.continuousOn.comp
    ((normalFiberHomeomorph_joint_continuous hχ huc hu hsmall).comp_continuousOn hcoords)
      (fun q hq => (normalFiberHomeomorph_helicoid_source hχ huc hu hsmall q.1.2 _).mp
        (helicoidFiberChart.map_target hq.2))

theorem helicoidAmbientIsotopy_inverse_joint_continuous :
    Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates =>
      (helicoidAmbientIsotopy hχ huc hu hsmall q.1.2).symm q.2) := by
  apply extendPartialMap_family_continuous
    (e := fun time : Icc (0 : ℝ) 1 => (helicoidAmbientPartial hχ huc hu hsmall time.2).symm)
    helicoidFiberChart.open_target helicoidFiberChart_half_support_closed
    helicoidFiberChart_half_support_subset (fun _ => rfl)
  · intro time y hy hn
    have hh := (helicoidAmbientPartial hχ huc hu hsmall time.2).left_inv hy
    rwa [helicoidAmbientPartial_fixes hχ huc hu hsmall time.2 hy hn] at hh
  · have hcoords : ContinuousOn (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates =>
        (q.1,helicoidFiberChart.symm q.2)) (univ ×ˢ helicoidFiberChart.target) :=
      continuous_fst.continuousOn.prodMk
        (helicoidFiberChart.continuousOn_symm.comp continuous_snd.continuousOn (fun _ h => h.2))
    change ContinuousOn (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates =>
      helicoidFiberChart ((normalFiberHomeomorph hχ huc hu hsmall q.1.2).symm
        (helicoidFiberChart.symm q.2))) (univ ×ˢ helicoidFiberChart.target)
    apply helicoidFiberChart.continuousOn.comp
      ((normalFiberHomeomorph_inverse_joint_continuous hχ huc hu hsmall).comp_continuousOn hcoords)
    intro q hq
    exact (homeomorph_symm_mem_iff (normalFiberHomeomorph hχ huc hu hsmall q.1.2)
      (normalFiberHomeomorph_helicoid_source hχ huc hu hsmall q.1.2)
      (helicoidFiberChart.symm q.2)).mpr (helicoidFiberChart.map_target hq.2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidAmbientIsotopy_joint_continuous
#print axioms TwoAxisHelicoid.helicoidAmbientIsotopy_inverse_joint_continuous
#print axioms TwoAxisHelicoid.helicoidAmbientIsotopy_time_one_graph
