import TwoAxisHelicoid.ImmersedTangentProjection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Either choice of orientation of a nearby tangent plane gives the
transversality of its unit normal with the reference normal fiber. -/
theorem nearby_core_normals_transverse {m n : SurfaceEuclideanSpace} (unit : ‖m‖=1)
    (near : ‖n-m‖<1 ∨ ‖n+m‖<1) : ⟪n,m⟫≠0 := by
  intro orth
  have mm : ⟪m,m⟫=1 := by rw [real_inner_self_eq_norm_sq,unit,one_pow]
  rcases near with h|h
  · have bound := abs_real_inner_le_norm (n-m) m
    rw [inner_sub_left,orth,mm,unit,mul_one] at bound
    norm_num at bound
    linarith
  · have bound := abs_real_inner_le_norm (n+m) m
    rw [inner_add_left,orth,mm,unit,mul_one] at bound
    norm_num at bound
    linarith

/-- Differentiate reconstruction in the actual tube. Every vector
killed by base projection is along the reference normal fiber. -/
theorem core_tube_base_kernel {X N : ℂ → SurfaceEuclideanSpace}
    {base : SurfaceEuclideanSpace → ℂ} {height : SurfaceEuclideanSpace → ℝ} {y : SurfaceEuclideanSpace}
    (x : DifferentiableAt ℝ X (base y)) (n : DifferentiableAt ℝ N (base y))
    (b : DifferentiableAt ℝ base y) (s : DifferentiableAt ℝ height y)
    (recovers : (fun p => X (base p)+height p • N (base p)) =ᶠ[𝓝 y] id)
    (v : SurfaceEuclideanSpace) (zero : fderiv ℝ base y v=0) :
    v=fderiv ℝ height y v • N (base y) := by
  have d := (x.hasFDerivAt.comp y b.hasFDerivAt).add (s.hasFDerivAt.smul (n.hasFDerivAt.comp y b.hasFDerivAt))
  have d' := (d.congr_of_eventuallyEq recovers.symm).unique (hasFDerivAt_id y)
  have eq := congrArg (fun A : SurfaceEuclideanSpace →L[ℝ] SurfaceEuclideanSpace => A v) d'
  simpa [zero] using eq.symm

/-- A regular sheet whose normal is transverse to the reference normal
fiber projects locally diffeomorphically to the base. The inverse
sheet has a genuine C¹ spatial extension in the base chart. -/
theorem transverse_core_normal_sheet {X N Y : ℂ → SurfaceEuclideanSpace}
    {base : SurfaceEuclideanSpace → ℂ} {height : SurfaceEuclideanSpace → ℝ} {z : ℂ}
    (sx : DifferentiableAt ℝ X (base (Y z))) (sn : DifferentiableAt ℝ N (base (Y z)))
    (sb : ContDiffAt ℝ 1 base (Y z)) (sh : DifferentiableAt ℝ height (Y z))
    (recovers : (fun p => X (base p)+height p • N (base p)) =ᶠ[𝓝 (Y z)] id)
    (sy : ContDiffAt ℝ 1 Y z) (imm : Function.Injective (fderiv ℝ Y z))
    (m : SurfaceEuclideanSpace) (perp : ∀ v, ⟪fderiv ℝ Y z v,m⟫=0)
    (angle : ⟪N (base (Y z)),m⟫≠0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z∈e.source ∧ (e : ℂ → ℂ)=base ∘ Y ∧
      ContDiffAt ℝ 1 (Y ∘ e.symm) (base (Y z)) := by
  let D := (fderiv ℝ base (Y z)).comp (fderiv ℝ Y z)
  have di : Function.Injective D := by
    apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective D.toLinearMap)
    apply LinearMap.ker_eq_bot'.mpr
    intro v h
    have v_eq := core_tube_base_kernel sx sn (sb.differentiableAt (by simp)) sh recovers (fderiv ℝ Y z v) h
    have ortho := perp v
    rw [v_eq,real_inner_smul_left] at ortho
    have ds := (mul_eq_zero.mp ortho).resolve_right angle
    exact imm ((v_eq.trans (by rw [ds,zero_smul])).trans (map_zero _).symm)
  have db : Function.Bijective D := ⟨di,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl (f := D.toLinearMap)).mp di⟩
  let A := (LinearEquiv.ofBijective D.toLinearMap db).toContinuousLinearEquiv
  let f := base ∘ Y
  have df : HasFDerivAt f A.toContinuousLinearMap z :=
    (sb.differentiableAt (by simp)).hasFDerivAt.comp z (sy.differentiableAt (by simp)).hasFDerivAt
  have sf : ContDiffAt ℝ 1 f z := sb.comp z sy
  have nz : (1:WithTop ℕ∞)≠0 := by simp
  let e := sf.toOpenPartialHomeomorph f df nz
  have near : z∈e.source := sf.mem_toOpenPartialHomeomorph_source df nz
  have back : e.symm (f z)=z := e.left_inv near
  have inverse : ContDiffAt ℝ 1 e.symm (f z) := sf.to_localInverse df nz
  have at_back : ContDiffAt ℝ 1 Y (e.symm (f z)) := by rwa [back]
  exact ⟨e,near,rfl,at_back.comp _ inverse⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nearby_core_normals_transverse
#print axioms TwoAxisHelicoid.core_tube_base_kernel
#print axioms TwoAxisHelicoid.transverse_core_normal_sheet
