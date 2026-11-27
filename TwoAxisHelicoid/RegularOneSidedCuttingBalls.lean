import TwoAxisHelicoid.HelicoidTangentBallSlabs
import TwoAxisHelicoid.RegularExtrinsicSphereCenters
import TwoAxisHelicoid.PositionalBoundedCurvatureGraph

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff Manifold RealInnerProductSpace

/-- The center can be chosen from any dense set. Moving it slightly
toward the empty half-space preserves the strict inequality on the
smaller closed ball, as well as the inner-ball incidence. -/
theorem one_sided_ball_with_dense_center {S D : Set SurfaceEuclideanSpace} (dense : Dense D)
    {x o n : SurfaceEuclideanSpace} {r d : ℝ} (rp : 0<r) (unit : ‖n‖=1) (near : dist x o<d)
    (side : ∀ y∈S∩closedBall o (4*r), 0<⟪y-o,n⟫) :
    ∃ c∈D, dist x c<d ∧ ∀ y∈S∩closedBall c (2*r), 0<⟪y-c,n⟫ := by
  let δ := min r (d-dist x o)/2
  have dp : 0<δ := half_pos (lt_min rp (sub_pos.mpr near))
  have dr : δ<r := (half_lt_self (lt_min rp (sub_pos.mpr near))).trans_le (min_le_left _ _)
  have dx : δ<d-dist x o := (half_lt_self (lt_min rp (sub_pos.mpr near))).trans_le (min_le_right _ _)
  let V := ball o r ∩ ball x d ∩ {c : SurfaceEuclideanSpace | ⟪c-o,n⟫<0}
  have openV : IsOpen V := (isOpen_ball.inter isOpen_ball).inter (isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const)
  let p := o-δ • n
  have diff : p-o= -(δ • n) := by dsimp [p]; abel
  have distp : dist p o=δ := by rw [dist_eq_norm,diff,norm_neg,norm_smul,Real.norm_of_nonneg dp.le,unit,mul_one]
  have vp : p∈V := by
    refine ⟨⟨mem_ball.mpr (distp.trans_lt dr),mem_ball.mpr (by linarith [dist_triangle p o x,dist_comm x o])⟩,?_⟩
    change ⟪p-o,n⟫<0
    rw [diff,inner_neg_left,real_inner_smul_left,real_inner_self_eq_norm_sq,unit,one_pow,mul_one]
    exact neg_neg_of_pos dp
  obtain ⟨c,cd,cc⟩ := dense.exists_mem_open openV ⟨p,vp⟩
  refine ⟨c,cd,(dist_comm x c).trans_lt (mem_ball.mp cc.1.2),?_⟩
  rintro y ⟨ys,yb⟩
  have yo : dist y o≤4*r := by linarith [dist_triangle y c o,mem_closedBall.mp yb,mem_ball.mp cc.1.1]
  have hy := side y ⟨ys,mem_closedBall.mpr yo⟩
  have down : ⟪c-o,n⟫<0 := cc.2
  rw [show y-c=(y-o)-(c-o) by abel,inner_sub_left]
  linarith

/-- In the singly normalized frame, the original positionally asymptotic
surface has single-scale one-sided test balls whose actual doubled
cutting sphere meets the immersed manifold transversely everywhere. -/
theorem original_exterior_regular_one_sided_balls (s : OriginalPositionallyAsymptoticHelicoid) {ε : ℝ} (ep : 0<ε) :
    let Y := centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
    let X := coordinateToEuclidean ∘ Y
    ∃ (r B : ℝ), 0<r ∧ ∀ x∈range X, B≤‖x‖ → ∃ c n : SurfaceEuclideanSpace,
      ‖n‖=1 ∧ dist x c<min ε 1*r ∧ (∀ y∈range X∩closedBall c (2*r), 0<⟪y-c,n⟫) ∧
        ∀ q : s.carrier, dist (X q) c=2*r → ∃ p : s.carrier, q∈(chartAt ℂ p).source ∧
          ∃ v : ℂ, ⟪coordinateToEuclidean (fderiv ℝ (Y ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) q) v),c-X q⟫≠0 := by
  intro Y X
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have a := (reference_frame_positional_standard _ s.axes.pitch_ne s.approaches).continuousLinearEquiv E
  rw [← range_comp,← range_comp] at a
  have ref : range (fun z : ℂ => coordinateToEuclidean (standardHelicoid z.re z.im))=euclideanHelicoidSet := by
    ext q
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.re,z.im,rfl⟩
    · rintro ⟨r,t,rfl⟩
      exact ⟨⟨r,t⟩,rfl⟩
  have approach : ApproachesSetAtInfinity (range X) euclideanHelicoidSet := ref ▸ a
  obtain ⟨r,B,rp,balls⟩ := approaching_helicoid_has_one_sided_balls approach ep
  let _ : SecondCountableTopology s.carrier := s.closedEmbedding.isEmbedding.secondCountableTopology
  have reg (p : s.carrier) : RegularImmersionChart Y (chartAt ℂ p) := by
    intro z hz
    obtain ⟨smooth,inj⟩ := smooth_surface_regular_manifold_chart s.smooth s.immersion p z hz
    have d := (R.toContinuousLinearMap.hasFDerivAt.comp z (smooth.differentiableAt (by simp)).hasFDerivAt).fderiv
    refine ⟨R.contDiff.contDiffAt.comp z smooth,?_⟩
    change Function.Injective (fderiv ℝ (R.toContinuousLinearMap ∘ (s.position ∘ (chartAt ℂ p).symm)) z)
    rw [d]
    exact R.injective.comp inj
  have dense := dense_regular_extrinsic_sphere_centers Y (chartAt ℂ) (mem_chart_source ℂ) reg (r := 2*r) (by positivity)
  refine ⟨r,B,rp,?_⟩
  intro x hx far
  obtain ⟨o,n,unit,near,side⟩ := balls x hx far
  obtain ⟨c,trans,xc,ys⟩ := one_sided_ball_with_dense_center dense rp unit near side
  exact ⟨c,n,unit,xc,ys,trans⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_sided_ball_with_dense_center
#print axioms TwoAxisHelicoid.original_exterior_regular_one_sided_balls
