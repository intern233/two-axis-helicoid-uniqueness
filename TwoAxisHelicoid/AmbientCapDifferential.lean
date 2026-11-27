import TwoAxisHelicoid.FlatEndCappingMap
import TwoAxisHelicoid.SmoothPlaneCapImmersion

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

noncomputable def capPlaneCoordinates : HelicoidTubeCoordinates →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).prod
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)

noncomputable def capNormalCoordinate : HelicoidTubeCoordinates →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

noncomputable def capNormalPart : HelicoidTubeCoordinates →L[ℝ] HelicoidTubeCoordinates :=
  ((0 : HelicoidTubeCoordinates →L[ℝ] ℝ).prod capNormalCoordinate).prod 0

theorem capPlaneCoordinates_apply (y : HelicoidTubeCoordinates) : capPlaneCoordinates y = (y.1.1,y.2) := rfl
theorem capNormalCoordinate_apply (y : HelicoidTubeCoordinates) : capNormalCoordinate y = y.1.2 := rfl
theorem capNormalPart_apply (y : HelicoidTubeCoordinates) : capNormalPart y = ((0,y.1.2),0) := rfl

theorem ambientPlaneCap_eq_split (A H : ℝ) (y : HelicoidTubeCoordinates) :
    ambientPlaneCap A H y = smoothPlaneCap A H (capPlaneCoordinates y)+capNormalPart y := by
  rw [capPlaneCoordinates_apply,capNormalPart_apply]
  ext <;> simp [ambientPlaneCap,smoothPlaneCap,add_comm]

theorem ambientPlaneCap_hasFDerivAt (A H : ℝ) (y : HelicoidTubeCoordinates) :
    HasFDerivAt (ambientPlaneCap A H)
      ((smoothPlaneCapDerivative A H (capPlaneCoordinates y)).comp capPlaneCoordinates+capNormalPart) y := by
  have hd := ((smoothPlaneCap_hasFDerivAt A H (capPlaneCoordinates y)).comp y
    capPlaneCoordinates.hasFDerivAt).add capNormalPart.hasFDerivAt
  have he : ambientPlaneCap A H = fun z => smoothPlaneCap A H (capPlaneCoordinates z)+capNormalPart z :=
    funext (ambientPlaneCap_eq_split A H)
  rw [he]
  simpa only using! hd

theorem ambientPlaneCap_fderiv_apply (A H : ℝ) (y v : HelicoidTubeCoordinates) :
    fderiv ℝ (ambientPlaneCap A H) y v =
      smoothPlaneCapDerivative A H (capPlaneCoordinates y) (capPlaneCoordinates v)+capNormalPart v := by
  rw [(ambientPlaneCap_hasFDerivAt A H y).fderiv]
  simp

theorem smoothPlaneCapDerivative_of_le {A H : ℝ} {p : ℝ × ℝ}
    (hp : p.1^2+p.2^2 ≤ A) (v : ℝ × ℝ) :
    smoothPlaneCapDerivative A H p v = ((v.1,0),v.2) := by
  have hq0 : 0 ≤ p.1^2+p.2^2 := by positivity
  simp [smoothPlaneCapDerivative,planeCapScale_deriv_zero hq0 hp,
    planeCapHeight_deriv_zero hq0 hp,planeCapScale_of_le hp]

theorem ambientPlaneCap_fderiv_inner {A H : ℝ} {y : HelicoidTubeCoordinates}
    (hy : y.1.1^2+y.2^2 ≤ A) :
    fderiv ℝ (ambientPlaneCap A H) y = ContinuousLinearMap.id ℝ HelicoidTubeCoordinates := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ambientPlaneCap_fderiv_apply,capPlaneCoordinates_apply,capPlaneCoordinates_apply,
    smoothPlaneCapDerivative_of_le hy,capNormalPart_apply]
  simp

theorem ambientPlaneCap_fderiv_tangent_kernel {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H)
    (y : HelicoidTubeCoordinates) {v : HelicoidTubeCoordinates} (hv : v.1.2 = 0)
    (hD : fderiv ℝ (ambientPlaneCap A H) y v = 0) : v = 0 := by
  rw [ambientPlaneCap_fderiv_apply,capNormalPart_apply,hv,show ((0,0),0) = (0 : HelicoidTubeCoordinates) from rfl,
    add_zero] at hD
  have he : capPlaneCoordinates v = 0 :=
    smoothPlaneCapDerivative_injective hA hH (capPlaneCoordinates y) (hD.trans (map_zero _).symm)
  have hx := congrArg (fun p : ℝ × ℝ => p.1) he
  have hz := congrArg (fun p : ℝ × ℝ => p.2) he
  exact Prod.ext (Prod.ext hx hv) hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ambientPlaneCap_fderiv_inner
#print axioms TwoAxisHelicoid.ambientPlaneCap_fderiv_tangent_kernel
