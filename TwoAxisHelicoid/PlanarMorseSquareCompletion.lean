import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace TwoAxisHelicoid
open Filter Topology Set
open scoped Topology ContDiff

/-- Complete the square for a variable nondegenerate quadratic form
near the origin. The resulting change of both planar coordinates is
a local C¹ diffeomorphism, even when the mixed coefficient is nonzero. -/
theorem planar_quadratic_coefficient_chart {A B C : ℝ × ℝ → ℝ}
    (sa : ContDiffAt ℝ 1 A 0) (sb : ContDiffAt ℝ 1 B 0) (sc : ContDiffAt ℝ 1 C 0)
    (s t : ℝ) (ss : s*s=1) (tt : t*t=1)
    (pa : 0<s*A 0) (pd : 0<t*(C 0-B 0^2/A 0)) :
    ∃ e : OpenPartialHomeomorph (ℝ×ℝ) (ℝ×ℝ),
      (0:ℝ×ℝ)∈e.source ∧ e 0=0 ∧ ContDiffAt ℝ 1 e 0 ∧ ContDiffAt ℝ 1 e.symm 0 ∧
      ∀ᶠ z : ℝ×ℝ in 𝓝 0, A z*z.1^2+2*B z*z.1*z.2+C z*z.2^2=s*(e z).1^2+t*(e z).2^2 := by
  let D := fun z => C z-B z^2/A z
  let k := fun z => B z/A z
  let u := fun z => Real.sqrt (s*A z)
  let v := fun z => Real.sqrt (t*D z)
  let F := fun z : ℝ×ℝ => (u z*(z.1+k z*z.2),v z*z.2)
  have a0 : A 0≠0 := (mul_ne_zero_iff.mp pa.ne').2
  have sk : ContDiffAt ℝ 1 k 0 := sb.div sa a0
  have sd : ContDiffAt ℝ 1 D 0 := sc.sub ((sb.pow 2).div sa a0)
  have su : ContDiffAt ℝ 1 u 0 := (contDiffAt_const.mul sa).sqrt pa.ne'
  have sv : ContDiffAt ℝ 1 v 0 := (contDiffAt_const.mul sd).sqrt pd.ne'
  have sf : ContDiffAt ℝ 1 F 0 :=
    (su.mul (contDiffAt_fst.add (sk.mul contDiffAt_snd))).prodMk (sv.mul contDiffAt_snd)
  let X := ContinuousLinearMap.fst ℝ ℝ ℝ
  let Y := ContinuousLinearMap.snd ℝ ℝ ℝ
  let L := (u 0 • (X+k 0 • Y)).prod (v 0 • Y)
  have hx : HasFDerivAt (Prod.fst : ℝ×ℝ → ℝ) X 0 := hasFDerivAt_fst
  have hy : HasFDerivAt (Prod.snd : ℝ×ℝ → ℝ) Y 0 := hasFDerivAt_snd
  have df : HasFDerivAt F L 0 := by
    simpa [F,L] using! (((su.differentiableAt one_ne_zero).hasFDerivAt.mul
      (hx.add ((sk.differentiableAt one_ne_zero).hasFDerivAt.mul hy))).prodMk
      ((sv.differentiableAt one_ne_zero).hasFDerivAt.mul hy))
  have up : u 0≠0 := (Real.sqrt_pos.mpr pa).ne'
  have vp : v 0≠0 := (Real.sqrt_pos.mpr pd).ne'
  have inj : Function.Injective L := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w eq
    have second : v 0*w.2=0 := congrArg Prod.snd eq
    have first : u 0*(w.1+k 0*w.2)=0 := congrArg Prod.fst eq
    have wz := (mul_eq_zero.mp second).resolve_left vp
    have wx := (mul_eq_zero.mp first).resolve_left up
    exact Prod.ext (by change w.1=0; simpa only [wz,mul_zero,add_zero] using wx) wz
  let E := (LinearEquiv.ofBijective L.toLinearMap
    ⟨inj,(LinearMap.injective_iff_surjective (f:=L.toLinearMap)).mp inj⟩).toContinuousLinearEquiv
  have de : HasFDerivAt F E.toContinuousLinearMap 0 := df
  let e := sf.toOpenPartialHomeomorph F de one_ne_zero
  have zero : e 0=0 := by change F 0=0; simp [F]
  refine ⟨e,sf.mem_toOpenPartialHomeomorph_source de one_ne_zero,zero,sf,
    zero ▸ (show ContDiffAt ℝ 1 e.symm (e 0) from sf.to_localInverse de one_ne_zero),?_⟩
  have posA : ∀ᶠ z in 𝓝 0, 0<s*A z := ((continuousAt_const (y:=s)).mul sa.continuousAt).eventually (Ioi_mem_nhds pa)
  have posD : ∀ᶠ z in 𝓝 0, 0<t*D z := ((continuousAt_const (y:=t)).mul sd.continuousAt).eventually (Ioi_mem_nhds pd)
  filter_upwards [posA,posD] with z ha hd
  have an := (mul_ne_zero_iff.mp ha.ne').2
  change _=s*(Real.sqrt (s*A z)*(z.1+k z*z.2))^2+t*(Real.sqrt (t*D z)*z.2)^2
  rw [mul_pow,mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hd.le]
  calc A z*z.1^2+2*B z*z.1*z.2+C z*z.2^2
      = A z*(z.1+k z*z.2)^2+D z*z.2^2 := by dsimp [D,k]; field_simp; ring
    _ = _ := by rw [← mul_assoc s,← mul_assoc s,ss,one_mul,← mul_assoc t,← mul_assoc t,tt,one_mul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_quadratic_coefficient_chart
