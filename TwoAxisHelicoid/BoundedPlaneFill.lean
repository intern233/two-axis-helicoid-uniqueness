module

public import TwoAxisHelicoid.MarkedExteriorComponent
import all TwoAxisHelicoid.MarkedExteriorComponent
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace TwoAxisHelicoid
open Set Metric Bornology Topology

/-- The open exterior of a ball is path connected in any real normed
space of rank at least two. A radial parametrization works up to the
sphere of radius zero. -/
theorem norm_ball_exterior_path_connected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dim : 1 < Module.rank ℝ E) {R : ℝ} (rp : 0≤R) : IsPathConnected {x : E | R<‖x‖} := by
  let radial (q : E × ℝ) := q.2 • q.1
  have sphere := isPathConnected_sphere dim (0:E) (r:=1) zero_le_one
  have radii : IsPathConnected (Ioi R) := (convex_Ioi R).isPathConnected nonempty_Ioi
  have image : radial '' (Metric.sphere (0:E) 1 ×ˢ Ioi R)={x : E | R<‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨u,r⟩,⟨on,above⟩,rfl⟩
      have unit : ‖u‖=1 := by simpa only [mem_sphere,dist_zero_right] using on
      have greater : R < r := mem_Ioi.mp above
      change R<‖r • u‖
      simpa only [norm_smul,unit,mul_one,Real.norm_of_nonneg (rp.trans greater.le)] using greater
    · intro outside
      have nz : ‖x‖≠0 := (rp.trans_lt outside).ne'
      refine ⟨((‖x‖⁻¹ : ℝ) • x,‖x‖),⟨?_,outside⟩,?_⟩
      · change dist ((‖x‖⁻¹ : ℝ) • x) 0=1
        rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),inv_mul_cancel₀ nz]
      · change ‖x‖ • ((‖x‖⁻¹ : ℝ) • x)=x
        rw [smul_smul,mul_inv_cancel₀ nz,one_smul]
  rw [←image]
  exact (sphere.prod radii).image (continuous_snd.smul continuous_fst)

/-- The set and all bounded components of its plane complement. -/
@[expose] def boundedPlaneFill (U : Set ℂ) := {x | IsBounded (connectedComponentIn Uᶜ x)}

theorem boundedPlaneFill_eq_exterior {U : Set ℂ} {R : ℝ} (rp : 0≤R)
    (bound : ∀ x∈U, ‖x‖≤R) {p : ℂ} (far : R<‖p‖) :
    boundedPlaneFill U=fillAwayFrom p U ∧ boundedPlaneFill U⊆closedBall 0 R := by
  let E := {z : ℂ | R<‖z‖}
  have out : E⊆Uᶜ := fun z hz zu => (bound z zu).not_gt hz
  have dim : 1 < Module.rank ℝ ℂ := by
    rw [←Module.finrank_eq_rank,Complex.finrank_real_complex]
    norm_num
  have comp : E⊆connectedComponentIn Uᶜ p :=
    (norm_ball_exterior_path_connected dim rp).isConnected.isPreconnected.subset_connectedComponentIn far out
  have unbounded : ¬IsBounded (connectedComponentIn Uᶜ p) := by
    intro bounded
    obtain ⟨B,bb⟩ := bounded.exists_norm_le
    let r := max B R+1
    have large : R<r := by dsimp [r]; linarith [le_max_right B R]
    have large' : B<r := by dsimp [r]; linarith [le_max_left B R]
    have norm : ‖(r:ℂ)‖=r := by rw [Complex.norm_real,Real.norm_of_nonneg (rp.trans large.le)]
    have outside : (r:ℂ)∈E := by change R<‖(r:ℂ)‖; rwa [norm]
    exact large'.not_ge (norm ▸ bb _ (comp outside))
  have eq : boundedPlaneFill U=fillAwayFrom p U := by
    ext x
    constructor
    · intro bounded inside
      exact unbounded ((connectedComponentIn_eq inside).symm ▸ bounded)
    · intro miss
      apply (isBounded_closedBall (x:=(0:ℂ)) (r:=R)).subset
      intro z hz
      apply mem_closedBall_zero_iff.mpr
      apply le_of_not_gt
      intro large
      have same := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq (comp large)).symm
      have inU : x∈Uᶜ := connectedComponentIn_nonempty_iff.mp ⟨z,hz⟩
      exact miss (same ▸ mem_connectedComponentIn inU)
  refine ⟨eq,?_⟩
  rw [eq]
  intro z hz
  exact mem_closedBall_zero_iff.mpr (le_of_not_gt fun far' => hz (comp far'))

theorem boundedPlaneFill_properties {U : Set ℂ} (bounded : IsBounded U) :
    U⊆boundedPlaneFill U ∧ IsBounded (boundedPlaneFill U) ∧
      IsPreconnected (boundedPlaneFill U)ᶜ ∧
      (IsOpen U → IsOpen (boundedPlaneFill U)) ∧
      (IsOpen U → IsConnected U → IsConnected (boundedPlaneFill U)) := by
  obtain ⟨B,b⟩ := bounded.exists_norm_le
  let R := max B 0
  have rp : 0≤R := le_max_right _ _
  let p : ℂ := (R+1:ℝ)
  have far : R<‖p‖ := by dsimp only [p]; rw [Complex.norm_real,Real.norm_of_nonneg (by linarith)]; linarith
  have bound (z : ℂ) (hz : z∈U) := (b z hz).trans (le_max_left B 0)
  obtain ⟨eq,small⟩ := boundedPlaneFill_eq_exterior rp bound far
  have size := isBounded_closedBall.subset small
  rw [eq] at size ⊢
  refine ⟨subset_fillAwayFrom _ _,size,?_,fun op => isOpen_fillAwayFrom op,?_⟩
  · simpa only [fillAwayFrom,compl_compl] using (isPreconnected_connectedComponentIn : IsPreconnected (connectedComponentIn Uᶜ p))
  · intro op conn
    apply fillAwayFrom_isConnected (fun hu => far.not_ge (bound _ hu)) op conn
    exact fun _ _ => (isOpen_fillAwayFrom op).connectedComponentIn

theorem boundedPlaneFill_homeomorph (e : ℂ ≃ₜ ℂ) (U : Set ℂ) :
    e '' boundedPlaneFill U=boundedPlaneFill (e '' U) := by
  have bounded_image (h : ℂ ≃ₜ ℂ) {S : Set ℂ} (bound : IsBounded S) : IsBounded (h '' S) :=
    (bound.isCompact_closure.image h.continuous).isBounded.subset (image_mono subset_closure)
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image]
  change IsBounded (connectedComponentIn Uᶜ x) ↔ IsBounded (connectedComponentIn (e '' U)ᶜ (e x))
  by_cases hu : x∈U
  · have off : x ∉ Uᶜ := fun h => h hu
    have offImage : e x ∉ (e '' U)ᶜ := fun h => h (mem_image_of_mem e hu)
    rw [connectedComponentIn_eq_empty off, connectedComponentIn_eq_empty offImage]
  · have eq := e.image_connectedComponentIn (show x∈Uᶜ from hu)
    rw [show e '' Uᶜ=(e '' U)ᶜ from e.toEquiv.image_compl _] at eq
    rw [←eq]
    refine ⟨bounded_image e, fun h => ?_⟩
    have back := bounded_image e.symm h
    have imageBack : e.symm '' (e '' connectedComponentIn Uᶜ x) = connectedComponentIn Uᶜ x :=
      e.toEquiv.symm_image_image _
    rwa [imageBack] at back

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.norm_ball_exterior_path_connected
#print axioms TwoAxisHelicoid.boundedPlaneFill_eq_exterior
#print axioms TwoAxisHelicoid.boundedPlaneFill_properties
#print axioms TwoAxisHelicoid.boundedPlaneFill_homeomorph
