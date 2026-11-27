import TwoAxisHelicoid.HelicoidEuclideanTube
import TwoAxisHelicoid.HelicoidNormalGeometry
import TwoAxisHelicoid.PositionalDistanceNormalTube
import TwoAxisHelicoid.NullEuclideanMetric

namespace TwoAxisHelicoid
open Set Metric Topology Real
open scoped RealInnerProductSpace

/-- Two empty tangent balls provide a uniform quadratic estimate for
every chord of the actual helicoid, at every reference point. -/
theorem euclidean_helicoid_chord_normal_bound (p : HelicoidEuclideanSpace) (hp : p∈euclideanHelicoidSet) :
    ∃ n : HelicoidEuclideanSpace, ‖n‖=1 ∧ ∀ q∈euclideanHelicoidSet, |⟪q-p,n⟫|≤dist q p^2 := by
  obtain ⟨r,θ,rfl⟩ := hp
  let p := euclideanHelicoid r θ
  let n : HelicoidEuclideanSpace := WithLp.toLp 2 (standardHelicoidNormal r θ)
  have un : ‖n‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq,one_pow]
    exact (standardHelicoid_unit_normal r θ).1
  have normal (s : ℝ) : euclideanHelicoidNormalMap r θ s=p+s • n :=
    congrArg (WithLp.toLp 2) (helicoidNormalMap_is_normal_displacement r θ s)
  refine ⟨n,un,?_⟩
  intro q hq
  have side (s : ℝ) (hs : |s|<1) : 2*s*⟪q-p,n⟫≤‖q-p‖^2 := by
    have near := infDist_le_dist_of_mem (x := euclideanHelicoidNormalMap r θ s) hq
    rw [euclideanHelicoidNormalMap_infDist hs,normal,dist_comm,dist_eq_norm,
      show q-(p+s • n)=(q-p)-s • n by abel] at near
    have squares := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr near
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,un,mul_one,Real.norm_eq_abs,sq_abs] at squares
    linarith
  apply abs_le.mpr
  change -‖q-p‖^2≤⟪q-p,n⟫ ∧ ⟪q-p,n⟫≤‖q-p‖^2
  constructor <;> linarith [side (1/2) (by norm_num),side (-(1/2)) (by norm_num)]

/-- At one fixed positive scale, a set approaching the helicoid only
in position has a strict supporting half-space in each ball at
infinity. The center of the ball lies on the supporting plane and
can be chosen within εr of the specified point. The larger ball of
radius 4r accommodates any regular intermediate cutting radius. -/
theorem approaching_helicoid_has_one_sided_balls {S : Set HelicoidEuclideanSpace}
    (asymptote : ApproachesSetAtInfinity S euclideanHelicoidSet) {ε : ℝ} (ep : 0<ε) :
    ∃ (r B : ℝ), 0<r ∧ ∀ x∈S, B≤‖x‖ →
      ∃ O n : HelicoidEuclideanSpace, ‖n‖=1 ∧ dist x O<min ε 1*r ∧
        ∀ y∈S∩closedBall O (4*r), 0<⟪y-O,n⟫ := by
  let r := min ε 1/200
  have rp : 0<r := by dsimp [r]; positivity
  have small : r≤1/200 := by dsimp [r]; gcongr; exact min_le_right _ _
  have r2 : r^2≤r/200 := by nlinarith [mul_le_mul_of_nonneg_left small rp.le]
  obtain ⟨b,near⟩ := asymptote (r^2) (sq_pos_of_pos rp)
  refine ⟨r,b+6,rp,?_⟩
  intro x hx far
  obtain ⟨p,ph,xp⟩ := near x hx (by linarith)
  obtain ⟨n,un,flat⟩ := euclidean_helicoid_chord_normal_bound p ph
  let O := p-(100*r^2) • n
  have op : dist p O=100*r^2 := by
    rw [dist_eq_norm,show p-O=(100*r^2) • n by dsimp [O]; abel,norm_smul,un,mul_one,Real.norm_of_nonneg (by positivity)]
  have xo : dist x O<min ε 1*r := by
    have e : min ε 1=200*r := by dsimp [r]; ring
    rw [e]
    nlinarith [dist_triangle x p O,sq_pos_of_pos rp]
  refine ⟨O,n,un,xo,?_⟩
  rintro y ⟨ys,yb⟩
  have yo : dist y O≤4*r := mem_closedBall.mp yb
  have yp : dist y p≤5*r := by linarith [dist_triangle y O p,dist_comm O p]
  have xy : dist x y≤6*r := by
    have e : min ε 1*r≤r := by simpa using mul_le_mul_of_nonneg_right (min_le_right ε 1) rp.le
    linarith [dist_triangle x O y,dist_comm O y]
  have yf : b≤‖y‖ := by linarith [show ‖x‖≤dist x y+‖y‖ by simpa using dist_triangle x y 0]
  obtain ⟨q,qh,yq⟩ := near y ys yf
  have qp : dist q p≤6*r := by linarith [dist_triangle q y p,dist_comm q y]
  have qsq := (sq_le_sq₀ dist_nonneg (by positivity)).mpr qp
  have height := (abs_le.mp (flat q qh)).1
  have err := abs_real_inner_le_norm (y-q) n
  rw [un,mul_one,← dist_eq_norm] at err
  have id : ⟪y-O,n⟫=⟪y-q,n⟫+⟪q-p,n⟫+100*r^2 := by
    rw [show y-O=(y-q)+(q-p)+(100*r^2) • n by dsimp [O]; abel,
      inner_add_left,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,un,one_pow,mul_one]
  rw [id]
  nlinarith [(abs_le.mp err).1,sq_pos_of_pos rp]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.euclidean_helicoid_chord_normal_bound
#print axioms TwoAxisHelicoid.approaching_helicoid_has_one_sided_balls
