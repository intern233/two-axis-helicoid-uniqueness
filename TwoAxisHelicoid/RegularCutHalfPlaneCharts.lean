import TwoAxisHelicoid.RegularCoreNormalCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace TwoAxisHelicoid
open Complex Set Metric
open scoped Topology ContDiff RealInnerProductSpace

/-- A smooth real submersion on a complex plane can itself be used
as the first real coordinate. The second coordinate is obtained by
rotating its derivative through a right angle in the source. -/
theorem regular_real_level_coordinate {u : ℂ → ℝ} {z : ℂ} (sm : ContDiffAt ℝ ∞ u z)
    (regular : ∃ v, fderiv ℝ u z v≠0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z∈e.source ∧ (∀ w, (e w).1=u w) ∧
      ContDiffAt ℝ ∞ e z ∧ ContDiffAt ℝ ∞ e.symm (e z) := by
  let A := fderiv ℝ u z
  let J : ℂ →L[ℝ] ℂ := I • (1 : ℂ →L[ℝ] ℂ)
  let B := A.comp J
  let D := A.prod B
  obtain ⟨w,non⟩ := regular
  have inj : Function.Injective D := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v zero
    by_contra nv
    have a : A v=0 := congrArg Prod.fst zero
    have b : A (I*v)=0 := congrArg Prod.snd zero
    let c := w/v
    have eq : c.re • v+c.im • (I*v)=w := by
      rw [Complex.real_smul,Complex.real_smul,← mul_assoc,← add_mul,Complex.re_add_im]
      exact div_mul_cancel₀ _ nv
    apply non
    change A w=0
    rw [← eq,map_add,map_smul,map_smul,a,b,smul_zero,smul_zero,zero_add]
  have dims : Module.finrank ℝ ℂ=Module.finrank ℝ (ℝ × ℝ) := by
    rw [Complex.finrank_real_complex,Module.finrank_prod,Module.finrank_self]
  let E := (LinearEquiv.ofBijective D.toLinearMap ⟨inj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims (f := D.toLinearMap)).mp inj⟩).toContinuousLinearEquiv
  let f := fun w : ℂ => (u w,B w)
  have df : HasFDerivAt f E.toContinuousLinearMap z :=
    (sm.differentiableAt (by simp)).hasFDerivAt.prodMk B.hasFDerivAt
  have sf : ContDiffAt ℝ ∞ f z := sm.prodMk B.contDiff.contDiffAt
  have nz : (∞ : WithTop ℕ∞)≠0 := by simp
  exact ⟨sf.toOpenPartialHomeomorph f df nz,sf.mem_toOpenPartialHomeomorph_source df nz,
    fun _ => rfl,sf,sf.to_localInverse df nz⟩

/-- At a transverse sphere all three cuts (open ball, boundary,
and closed ball) are the corresponding half-plane cuts in a single
smooth coordinate on the immersed surface. -/
theorem transverse_sphere_has_half_plane_chart {X : ℂ → SurfaceEuclideanSpace} {c : SurfaceEuclideanSpace}
    {z : ℂ} {r : ℝ} (rp : 0<r) (sm : ContDiffAt ℝ ∞ X z) (level : dist (X z) c=r)
    (trans : ∃ v, ⟪fderiv ℝ X z v,c-X z⟫≠0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z∈e.source ∧ (e z).1=0 ∧
      ContDiffAt ℝ ∞ e z ∧ ContDiffAt ℝ ∞ e.symm (e z) ∧
      ∀ w, (X w∈ball c r ↔ (e w).1<0) ∧ (X w∈sphere c r ↔ (e w).1=0) ∧
        (X w∈closedBall c r ↔ (e w).1≤0) := by
  let u := fun w : ℂ => ‖X w-c‖^2-r^2
  have su : ContDiffAt ℝ ∞ u z := ((sm.sub contDiffAt_const).norm_sq ℝ).sub contDiffAt_const
  obtain ⟨v,hv⟩ := trans
  have diff := (((sm.differentiableAt (by simp)).hasFDerivAt.sub_const c).norm_sq).sub_const (r^2)
  have nz : fderiv ℝ u z v≠0 := by
    rw [show fderiv ℝ u z=_ from diff.fderiv]
    simp only [ContinuousLinearMap.comp_apply,smul_apply]
    change (2 : ℕ) • ⟪X z-c,fderiv ℝ X z v⟫≠0
    rw [two_nsmul]
    intro h
    apply hv
    rw [← neg_sub (X z) c,inner_neg_right,real_inner_comm]
    linarith
  obtain ⟨e,inside,coord,ef,eb⟩ := regular_real_level_coordinate su ⟨v,nz⟩
  have form (w : ℂ) : (e w).1=dist (X w) c^2-r^2 := by rw [coord,dist_eq_norm]
  refine ⟨e,inside,by rw [form,level,sub_self],ef,eb,?_⟩
  intro w
  rw [form,mem_ball,mem_sphere,mem_closedBall]
  have nn := dist_nonneg (x := X w) (y := c)
  constructor
  · constructor <;> intro h <;> nlinarith
  constructor <;> constructor <;> intro h <;> nlinarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_real_level_coordinate
#print axioms TwoAxisHelicoid.transverse_sphere_has_half_plane_chart
