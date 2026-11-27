import TwoAxisHelicoid.HelicoidHeightGraphTangents
import TwoAxisHelicoid.OrientedSpatialPoleFrame
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Matrix Set Metric Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- In the conformal coordinates (x,y) ↦ (sinh x,y), the base Gauss
map has speed at most one. This bound is uniform even along the axis. -/
theorem conformal_helicoid_normal_distance (a z : ℂ) :
    ‖coordinateToEuclidean (conformalHelicoidNormal z)-coordinateToEuclidean (conformalHelicoidNormal a)‖≤‖z-a‖ := by
  let v := z-a
  let p := fun t : ℝ => a+t • v
  let n := fun t : ℝ => coordinateToEuclidean (conformalHelicoidNormal (p t))
  let h := fun t : ℝ => Real.cosh (p t).re
  let R := fun t : ℝ => Real.sinh (p t).re
  let θ := fun t : ℝ => (p t).im
  let N := fun (t : ℝ) (j : Fin 3) => (h t*v.re)/(helicoidQ (R t))^3*standardHelicoidTheta (R t) (θ t) j+
    v.im/helicoidQ (R t)*standardHelicoidR (θ t) j
  have d (t : ℝ) : HasDerivAt n (coordinateToEuclidean (N t)) t := by
    have line : HasDerivAt p v t := by
      simpa only [one_smul] using ((hasDerivAt_id' t).smul_const v).const_add a
    have dr := (Real.hasDerivAt_sinh _).comp t (reCLM.hasFDerivAt.comp_hasDerivAt t line)
    have dθ := imCLM.hasFDerivAt.comp_hasDerivAt t line
    exact coordinateToEuclidean.hasFDerivAt.comp_hasDerivAt t (standardHelicoidNormal_curve_hasDerivAt dr dθ)
  have bound (t : ℝ) (_ : t∈Ico (0:ℝ) 1) : ‖coordinateToEuclidean (N t)‖≤‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j,(N t j)^2)≤‖v‖^2
    unfold N
    rw [standardHelicoid_normal_differential_metric,show helicoidQ (R t)=h t from helicoidQ_sinh _]
    have den : 0<(h t)^4 := pow_pos (Real.cosh_pos _) _
    apply (div_le_iff₀ den).mpr
    have eq : (h t*v.re)^2+(h t)^2*v.im^2=(h t)^2*‖v‖^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      ring
    rw [eq,mul_comm ((h t)^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Real.one_le_cosh _) (by decide : 2≤4)) (sq_nonneg _)
  have est := norm_image_sub_le_of_norm_deriv_le_segment' (fun t _ => (d t).hasDerivWithinAt)
    bound 1 (right_mem_Icc.mpr zero_le_one)
  simpa only [n,p,one_smul,zero_smul,add_zero,v,add_sub_cancel,mul_one,sub_zero] using est

/-- The frame chosen at the center of the physical parameter disk
makes the negative base normal its north pole. -/
theorem helicoid_frame_away_from_base_normal (a : ℂ) :
    ∃ T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ), (∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y) ∧
      (∀ x y, T x ⨯₃ T y=T (x ⨯₃ y)) ∧ ∀ v, T v 2= -(conformalHelicoidNormal a ⬝ᵥ v) := by
  let r := Real.sinh a.re
  let θ := a.im
  let Q := helicoidQ r
  let A := standardHelicoidR θ
  let V := standardHelicoidTheta r θ
  let B := (-1/Q) • V
  obtain ⟨met,perp,vm⟩ := standardHelicoid_metric r θ
  have aa : A ⬝ᵥ A=1 := by simpa only [dotProduct,← sq] using met
  have ab : A ⬝ᵥ B=0 := by
    change A ⬝ᵥ ((-1/Q) • V)=0
    rw [dotProduct_smul,show A ⬝ᵥ V=0 from perp,smul_zero]
  have vv : V ⬝ᵥ V=Q^2 := by simpa only [dotProduct,← sq] using vm
  have qp : Q≠0 := (helicoidQ_pos r).ne'
  have bb : B ⬝ᵥ B=1 := by
    change ((-1/Q) • V) ⬝ᵥ ((-1/Q) • V)=1
    rw [smul_dotProduct,dotProduct_smul,vv]
    simp only [smul_eq_mul]
    field_simp
  obtain ⟨T,ortho,cross,last⟩ := oriented_frame_with_last_normal A B aa bb ab
  refine ⟨T,ortho,cross,fun v => ?_⟩
  have basis : A ⨯₃ B= -conformalHelicoidNormal a := by
    change A ⨯₃ ((-1/Q) • V)=_
    rw [map_smul,show A ⨯₃ V=Q • conformalHelicoidNormal a from helicoid_base_cross r θ,smul_smul]
    rw [div_mul_cancel₀ _ qp,neg_one_smul]
  rw [last,basis,neg_dotProduct]

/-- A half-width graph over this helicoid omits a spherical cap in
the same actual spatial frame throughout a fixed parameter disk. -/
theorem physical_height_graph_disk_frame {u : ℝ × ℝ → ℝ} {a : ℂ} {R : ℝ}
    (radius : R≤15/16)
    (du : ∀ z∈ball a R, DifferentiableAt ℝ u (helicoidConformalBase z))
    (half : ∀ z∈ball a R, |u (helicoidConformalBase z)|≤1/2) :
    ∃ T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ), (∀ x y, T x ⬝ᵥ T y=x ⬝ᵥ y) ∧
      (∀ x y, T x ⨯₃ T y=T (x ⨯₃ y)) ∧ ∀ z∈ball a R,
        unitCrossNormal (fderiv ℝ (T ∘ helicoidHeightSurface u) z 1) (fderiv ℝ (T ∘ helicoidHeightSurface u) z I) 2≤15/16 := by
  obtain ⟨T,ortho,cross,last⟩ := helicoid_frame_away_from_base_normal a
  refine ⟨T,ortho,cross,fun z hz => ?_⟩
  let X := helicoidHeightSurface u
  let D := fderiv ℝ X z
  let n := unitCrossNormal (D 1) (D I)
  have inj : Function.Injective D := by
    intro v w eq
    have h := physical_height_graph_speed_lower (du z hz) (half z hz) (v-w)
    change ‖v-w‖≤2*‖coordinateToEuclidean (D (v-w))‖ at h
    rw [map_sub,eq,sub_self,map_zero,norm_zero,mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have unit : ‖coordinateToEuclidean n‖=1 := by
    rw [← euclidean_chart_normal_eq_unitCross X z]
    exact euclideanUnitChartNormal_unit inj
  have dot (x y : Fin 3 → ℝ) : ⟪coordinateToEuclidean x,coordinateToEuclidean y⟫=x ⬝ᵥ y := by
    rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]
  have b := real_inner_le_norm (coordinateToEuclidean (conformalHelicoidNormal z)-coordinateToEuclidean (conformalHelicoidNormal a))
    (coordinateToEuclidean n)
  rw [inner_sub_left,dot,dot,unit,mul_one] at b
  have near : ‖z-a‖<R := by simpa only [mem_ball,dist_eq_norm] using hz
  have pos : 0<conformalHelicoidNormal z ⬝ᵥ n := physical_height_graph_normal_positive (du z hz) (half z hz)
  rw [oriented_spatial_frame_normal ortho cross,last]
  change -(conformalHelicoidNormal a ⬝ᵥ n)≤_
  linarith [conformal_helicoid_normal_distance a z]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformal_helicoid_normal_distance
#print axioms TwoAxisHelicoid.physical_height_graph_disk_frame
