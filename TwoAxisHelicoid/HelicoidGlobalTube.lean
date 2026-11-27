import TwoAxisHelicoid.HelicoidTubeSmooth
import TwoAxisHelicoid.HelicoidEuclideanTube

namespace TwoAxisHelicoid
open Real Set Filter Metric
open scoped Topology ContDiff

def helicoidTubeStrip : Set HelicoidTubeCoordinates := {p | |p.1.1| < 1}

theorem helicoidTubeStrip_isOpen : IsOpen helicoidTubeStrip :=
  isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_fst)) continuous_const

theorem helicoidTubeMap_injOn : InjOn helicoidTubeMap helicoidTubeStrip := by
  intro p hp q hq he
  have hh := congrArg (fun z : HelicoidTubeCoordinates => (z.1.1,z.1.2,z.2)) he
  change helicoidNormalMap p.1.2 p.2 p.1.1 = helicoidNormalMap q.1.2 q.2 q.1.1 at hh
  obtain ⟨hr,hθ,hs⟩ := helicoidNormalMap_injective hp hq hh
  exact Prod.ext (Prod.ext hs hr) hθ

noncomputable def helicoidTubeEquiv : PartialEquiv HelicoidTubeCoordinates HelicoidTubeCoordinates :=
  helicoidTubeMap_injOn.toPartialEquiv helicoidTubeMap helicoidTubeStrip

theorem helicoidTubeEquiv_local_inverse {p : HelicoidTubeCoordinates}
    (hp : p ∈ helicoidTubeEquiv.source) :
    helicoidTubeEquiv.target ∈ 𝓝 (helicoidTubeMap p) ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidTubeEquiv.symm (helicoidTubeMap p) := by
  obtain ⟨e,he,heq,hsmooth⟩ := helicoidTubeMap_local_diffeomorph hp
  have hepoint : e p = helicoidTubeMap p := congrFun heq p
  have ht : helicoidTubeMap p ∈ e.target := by rw [← hepoint]; exact e.map_source he
  have hback : e.symm (helicoidTubeMap p) = p := by rw [← hepoint]; exact e.left_inv he
  have hsrc : ∀ᶠ y in 𝓝 (helicoidTubeMap p), e.symm y ∈ helicoidTubeEquiv.source := by
    apply (e.continuousAt_symm ht).eventually
    rw [hback]
    exact helicoidTubeStrip_isOpen.mem_nhds hp
  have htarget := e.open_target.mem_nhds ht
  have hsame : helicoidTubeEquiv.symm =ᶠ[𝓝 (helicoidTubeMap p)] e.symm := by
    filter_upwards [hsrc,htarget] with y hys hyt
    have hy : helicoidTubeEquiv (e.symm y) = y := by
      change helicoidTubeMap (e.symm y) = y
      rw [← heq]
      exact e.right_inv hyt
    calc
      helicoidTubeEquiv.symm y = helicoidTubeEquiv.symm (helicoidTubeEquiv (e.symm y)) :=
        congrArg helicoidTubeEquiv.symm hy.symm
      _ = e.symm y := helicoidTubeEquiv.left_inv hys
  refine ⟨?_,hsmooth.congr_of_eventuallyEq hsame⟩
  filter_upwards [hsrc,htarget] with y hys hyt
  have hh := helicoidTubeEquiv.map_source hys
  change helicoidTubeMap (e.symm y) ∈ helicoidTubeEquiv.target at hh
  rw [← heq,e.right_inv hyt] at hh
  exact hh

theorem helicoidTubeEquiv_target_isOpen : IsOpen helicoidTubeEquiv.target := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have h := (helicoidTubeEquiv_local_inverse (helicoidTubeEquiv.map_target hy)).1
  change helicoidTubeEquiv.target ∈ 𝓝 (helicoidTubeEquiv (helicoidTubeEquiv.symm y)) at h
  rw [helicoidTubeEquiv.right_inv hy] at h
  exact h

theorem helicoidTubeEquiv_inverse_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidTubeEquiv.symm y := by
  have h := (helicoidTubeEquiv_local_inverse (helicoidTubeEquiv.map_target hy)).2
  change ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidTubeEquiv.symm
    (helicoidTubeEquiv (helicoidTubeEquiv.symm y)) at h
  rw [helicoidTubeEquiv.right_inv hy] at h
  exact h

/-- The global normal coordinates on the entire width-one tube, with a
continuous inverse. The inverse is smooth throughout its open target. -/
noncomputable def helicoidGlobalTube :
    OpenPartialHomeomorph HelicoidTubeCoordinates HelicoidTubeCoordinates where
  toPartialEquiv := helicoidTubeEquiv
  continuousOn_toFun := helicoidTubeMap_contDiff.continuous.continuousOn
  continuousOn_invFun := fun _ hy => (helicoidTubeEquiv_inverse_contDiffAt hy).continuousAt.continuousWithinAt
  open_source := helicoidTubeStrip_isOpen
  open_target := helicoidTubeEquiv_target_isOpen

noncomputable def helicoidSignedDistance (y : HelicoidTubeCoordinates) : ℝ :=
  (helicoidTubeEquiv.symm y).1.1

theorem helicoidSignedDistance_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidSignedDistance y :=
  (helicoidTubeEquiv_inverse_contDiffAt hy).fst.fst

theorem helicoidSignedDistance_on_normal {p : HelicoidTubeCoordinates}
    (hp : p ∈ helicoidTubeStrip) : helicoidSignedDistance (helicoidTubeMap p) = p.1.1 := by
  change (helicoidTubeEquiv.symm (helicoidTubeEquiv p)).1.1 = p.1.1
  rw [helicoidTubeEquiv.left_inv hp]

theorem helicoidTubeEquiv_target_iff_distance {y : HelicoidTubeCoordinates} :
    y ∈ helicoidTubeEquiv.target ↔
      infDist (helicoidEuclideanPoint (y.1.1,y.1.2,y.2)) euclideanHelicoidSet < 1 := by
  rw [euclideanHelicoid_distance_lt_one_iff]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p.1.2,p.2,p.1.1,hp,rfl⟩
  · rintro ⟨r,θ,s,hs,he⟩
    refine ⟨((s,r),θ),hs,?_⟩
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun p : HelicoidEuclideanSpace => p 0) he
      · exact congrArg (fun p : HelicoidEuclideanSpace => p 1) he
    · exact congrArg (fun p : HelicoidEuclideanSpace => p 2) he

theorem helicoidSignedDistance_abs_eq_infDist {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    |helicoidSignedDistance y| =
      infDist (helicoidEuclideanPoint (y.1.1,y.1.2,y.2)) euclideanHelicoidSet := by
  let p := helicoidTubeEquiv.symm y
  have hp : p ∈ helicoidTubeStrip := helicoidTubeEquiv.map_target hy
  have he : helicoidTubeMap p = y := helicoidTubeEquiv.right_inv hy
  rw [← he]
  rw [helicoidSignedDistance_on_normal hp]
  exact (euclideanHelicoidNormalMap_infDist hp).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidTubeEquiv_inverse_contDiffAt
#print axioms TwoAxisHelicoid.helicoidSignedDistance_abs_eq_infDist
