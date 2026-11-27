import TwoAxisHelicoid.MarkedTorusAngularEscape
import TwoAxisHelicoid.HorizontalLineSchwarz
import TwoAxisHelicoid.CoordinateOrientationIsometry
import TwoAxisHelicoid.HorizontalLineEndOrders
import TwoAxisHelicoid.SpatialSimilarityClasses

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

theorem scalar_harmonic_conformal_chart {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) (conf : ConformalCoordinateDerivatives X z)
    (imm : Function.Injective (fderiv ℝ X z)) {k : ℝ} (hk : k≠0) :
    let Y := fun w => k • X w
    (∀ j, HarmonicAt (fun w => Y w j) z) ∧ ConformalCoordinateDerivatives Y z ∧ Function.Injective (fderiv ℝ Y z) := by
  have dx := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh j)).differentiableAt
  have d := dx.hasFDerivAt.const_smul k
  refine ⟨fun j => (hh j).comp_CLM (k • ContinuousLinearMap.id ℝ ℝ),?_,?_⟩
  · apply (conformalCoordinateDerivatives_iff_dot d.differentiableAt).mpr
    obtain ⟨eq,ort⟩ := (conformalCoordinateDerivatives_iff_dot dx).mp conf
    rw [d.fderiv]
    simp only [smul_apply,smul_dotProduct,dotProduct_smul,smul_eq_mul,eq,ort,mul_zero,and_self]
  · have hd : fderiv ℝ (fun w => k • X w) z=k • fderiv ℝ X z := d.fderiv
    rw [hd]
    exact fun _ _ h => imm ((smul_right_injective _ hk) h)

theorem reference_frame_scaled_rotation {α : ℝ} (ha : α≠0) (x : Fin 3 → ℝ) :
    axisSpatialNormalization ha ![0,0,0] x=α • lineAxisCoordinates (-1) (by simp) 0 x := by
  apply coordinateToTube_injective
  rw [axis_normalized_tube_vector]
  apply Prod.ext
  · apply Prod.ext
    · change -α*x 0=α*((starRingEnd ℂ (-1)).re*(x 0-0)-(starRingEnd ℂ (-1)).im*(x 1-0))
      simp
    · change -α*x 1=α*((starRingEnd ℂ (-1)).im*(x 0-0)+(starRingEnd ℂ (-1)).re*(x 1-0))
      simp
  · change α*(x 2-0)=α*(x 2-0)
    rfl

theorem reference_frame_harmonic_chart {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) (conf : ConformalCoordinateDerivatives X z)
    (imm : Function.Injective (fderiv ℝ X z)) {α : ℝ} (ha : α≠0) :
    let Y := axisSpatialNormalization ha ![0,0,0] ∘ X
    (∀ j, HarmonicAt (fun w => Y w j) z) ∧ ConformalCoordinateDerivatives Y z ∧ Function.Injective (fderiv ℝ Y z) := by
  let R := lineAxisCoordinates (-1) (by simp) 0
  obtain ⟨h,c,i⟩ := lineAxisCoordinates_harmonic_chart (-1) (by simp) 0 hh conf imm
  have eq : axisSpatialNormalization ha ![0,0,0] ∘ X=(fun w => α • R (X w)) :=
    funext fun w => reference_frame_scaled_rotation ha _
  rw [eq]
  exact scalar_harmonic_conformal_chart h c i ha

/-- The physical pitch normalization is an actual bijective metric
dilation in Euclidean coordinates, also for negative pitches. -/
theorem reference_frame_euclidean_dilation {α : ℝ} (ha : α≠0) :
    ∃ F : EuclideanSpace ℝ (Fin 3) ≃ᵈ EuclideanSpace ℝ (Fin 3), ∀ p,
      F (coordinateToEuclidean p)=coordinateToEuclidean (axisSpatialNormalization ha ![0,0,0] p) := by
  let R := lineAxisCoordinates (-1) (by simp) 0
  let E := euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq (-1) (by simp) 0)
  refine ⟨E.toDilationEquiv.trans (DilationEquiv.smulTorsor 0 ha),fun p => ?_⟩
  rw [reference_frame_scaled_rotation]
  change α • coordinateToEuclidean (R p)+0=coordinateToEuclidean (α • R p)
  rw [add_zero]
  rfl

theorem reference_frame_maps_straight_axes {α : ℝ} (ha : α≠0) {S : Set (Fin 3 → ℝ)}
    (d : ℂ) (A : Fin 3 → ℝ) (line : ∀ r : ℝ, A+r • ![d.re,d.im,0]∈S)
    (vert : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈S) :
    let R := axisSpatialNormalization ha ![0,0,0]
    (∀ r : ℝ, R A+r • ![d.re,d.im,0]∈R '' S) ∧ (∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈R '' S) := by
  let R := axisSpatialNormalization ha ![0,0,0]
  constructor
  · intro r
    refine ⟨_,line (-(r/α)),?_⟩
    apply coordinateToTube_injective
    rw [axis_normalized_tube_vector]
    have v := axis_normalized_tube_vector ha 0 A
    have x := congrArg (fun p : HelicoidTubeCoordinates => p.1.1) v
    have y := congrArg (fun p : HelicoidTubeCoordinates => p.1.2) v
    have z := congrArg Prod.snd v
    change R A 0= -α*A 0 at x
    change R A 1= -α*A 1 at y
    change R A 2=α*(A 2-0) at z
    change ((-α*(A 0+ -(r/α)*d.re),-α*(A 1+ -(r/α)*d.im)),α*(A 2+ -(r/α)*0-0))=
      ((R A 0+r*d.re,R A 1+r*d.im),R A 2+r*0)
    rw [x,y,z]
    congr 2 <;> field_simp [ha] <;> ring
  · intro r
    refine ⟨_,vert (r/α),?_⟩
    apply coordinateToTube_injective
    rw [axis_normalized_tube_vector]
    change ((-α*0,-α*0),α*(r/α-0))=((0,0),r)
    simp only [mul_zero,sub_zero,Prod.mk.injEq,true_and]
    field_simp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.reference_frame_harmonic_chart
