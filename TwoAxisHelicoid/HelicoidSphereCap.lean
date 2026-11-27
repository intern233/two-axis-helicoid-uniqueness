import TwoAxisHelicoid.HelicoidTubeSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Real Set Metric
open scoped ContDiff
set_option maxHeartbeats 1000000

/-- The ordinary Euclidean squared radius, in the product coordinates
used by the helicoid tube. It is not the product-space norm squared. -/
def ambientRadiusSq (y : HelicoidTubeCoordinates) : ℝ :=
  y.1.1^2+y.1.2^2+y.2^2

theorem ambientRadiusSq_continuous : Continuous ambientRadiusSq := by
  unfold ambientRadiusSq
  fun_prop

theorem helicoidTubeRotation_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞)
    helicoidTubeRotation := by
  change ContDiff ℝ (∞ : WithTop ℕ∞) (fun p : HelicoidTubeCoordinates =>
    ((p.1.1*cos p.2-p.1.2*sin p.2,p.1.1*sin p.2+p.1.2*cos p.2),p.2))
  fun_prop

theorem helicoidTubeRotation_radius (y : HelicoidTubeCoordinates) :
    ambientRadiusSq (helicoidTubeRotation y) = ambientRadiusSq y := by
  dsimp [ambientRadiusSq,helicoidTubeRotation]
  nlinarith [congrArg (fun a : ℝ => y.1.1^2*a) (sin_sq_add_cos_sq y.2),
    congrArg (fun a : ℝ => y.1.2^2*a) (sin_sq_add_cos_sq y.2)]

theorem helicoidTubeMap_zero_eq_rotation (p : ℝ × ℝ) :
    helicoidTubeMap ((0,p.1),p.2) = helicoidTubeRotation ((p.1,0),p.2) := by
  simp [helicoidTubeMap,helicoidNormalMap,helicoidTubeRotation,helicoidAngle]

theorem helicoidTubeMap_zero_radius (p : ℝ × ℝ) :
    ambientRadiusSq (helicoidTubeMap ((0,p.1),p.2)) = p.1^2+p.2^2 := by
  rw [helicoidTubeMap_zero_eq_rotation,helicoidTubeRotation_radius]
  simp [ambientRadiusSq]

def euclideanParameterDisk (R : ℝ) : Set (ℝ × ℝ) := {p | p.1^2+p.2^2 ≤ R^2}

theorem euclideanParameterDisk_isCompact (R : ℝ) : IsCompact (euclideanParameterDisk R) := by
  apply (isCompact_closedBall (0 : ℝ × ℝ) |R|).of_isClosed_subset
  · exact isClosed_le (by fun_prop) continuous_const
  · intro p hp
    rw [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
    change p.1^2+p.2^2 ≤ R^2 at hp
    constructor
    · change |p.1| ≤ |R|
      exact (sq_le_sq).mp (by nlinarith [sq_nonneg p.2])
    · change |p.2| ≤ |R|
      exact (sq_le_sq).mp (by nlinarith [sq_nonneg p.1])

/-- An explicit disk on the actual sphere, bounded by the helicoid's
spherical section. Untwisting turns it into the upper hemisphere. -/
noncomputable def helicoidSphereCap (R : ℝ) (p : ℝ × ℝ) : HelicoidTubeCoordinates :=
  helicoidTubeRotation ((p.1,sqrt (R^2-p.1^2-p.2^2)),p.2)

theorem helicoidSphereCap_continuous (R : ℝ) : Continuous (helicoidSphereCap R) := by
  unfold helicoidSphereCap
  exact helicoidTubeRotation.continuous.comp (by fun_prop)

theorem helicoidSphereCap_injective (R : ℝ) : Function.Injective (helicoidSphereCap R) := by
  intro p q h
  have he := helicoidTubeRotation.injective h
  exact Prod.ext (congrArg (fun y : HelicoidTubeCoordinates => y.1.1) he)
    (congrArg (fun y : HelicoidTubeCoordinates => y.2) he)

theorem helicoidSphereCap_radius {R : ℝ} {p : ℝ × ℝ} (hp : p ∈ euclideanParameterDisk R) :
    ambientRadiusSq (helicoidSphereCap R p) = R^2 := by
  rw [helicoidSphereCap,helicoidTubeRotation_radius]
  have hh : 0 ≤ R^2-p.1^2-p.2^2 := by change p.1^2+p.2^2 ≤ R^2 at hp; linarith
  dsimp [ambientRadiusSq]
  rw [sq_sqrt hh]
  ring

theorem helicoidSphereCap_boundary {R : ℝ} {p : ℝ × ℝ} (hp : p.1^2+p.2^2 = R^2) :
    helicoidSphereCap R p = helicoidTubeMap ((0,p.1),p.2) := by
  rw [helicoidTubeMap_zero_eq_rotation]
  have hz : R^2-p.1^2-p.2^2 = 0 := by linarith
  simp [helicoidSphereCap,hz]

theorem helicoidSphereCap_contDiffOn_interior (R : ℝ) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (helicoidSphereCap R) {p | p.1^2+p.2^2 < R^2} := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply helicoidTubeRotation_contDiff.contDiffAt.comp
  have hh : R^2-p.1^2-p.2^2 ≠ 0 := by dsimp at hp; linarith
  exact (contDiffAt_fst.prodMk
    (((contDiffAt_const.sub (contDiffAt_fst.pow 2)).sub (contDiffAt_snd.pow 2)).sqrt hh)).prodMk
      contDiffAt_snd

theorem helicoidSphereCap_isEmbedding (R : ℝ) :
    Topology.IsEmbedding (fun p : euclideanParameterDisk R => helicoidSphereCap R p.1) := by
  let := isCompact_iff_compactSpace.mp (euclideanParameterDisk_isCompact R)
  exact ((helicoidSphereCap_continuous R).comp continuous_subtype_val |>.isClosedEmbedding
    ((helicoidSphereCap_injective R).comp Subtype.val_injective)).isEmbedding

theorem helicoidSphereCap_mem_helicoid_iff {R : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ euclideanParameterDisk R) :
    (∃ q : ℝ × ℝ, helicoidTubeMap ((0,q.1),q.2) = helicoidSphereCap R p) ↔
      p.1^2+p.2^2 = R^2 := by
  constructor
  · rintro ⟨q,hq⟩
    rw [helicoidTubeMap_zero_eq_rotation] at hq
    have he := helicoidTubeRotation.injective hq
    have hz : 0 = sqrt (R^2-p.1^2-p.2^2) :=
      congrArg (fun y : HelicoidTubeCoordinates => y.1.2) he
    have hh := Real.sqrt_eq_zero'.mp hz.symm
    change p.1^2+p.2^2 ≤ R^2 at hp
    linarith
  · intro hp
    exact ⟨p,(helicoidSphereCap_boundary hp).symm⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidSphereCap_isEmbedding
#print axioms TwoAxisHelicoid.helicoidSphereCap_boundary
