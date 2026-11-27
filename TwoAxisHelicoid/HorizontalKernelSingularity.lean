import TwoAxisHelicoid.ExponentialPoleEssential
import TwoAxisHelicoid.ZetaPoleRegular
import TwoAxisHelicoid.HorizontalRightValue
import TwoAxisHelicoid.CoordinateDataSymmetry
import TwoAxisHelicoid.SinglePunctureEndFlux

namespace TwoAxisHelicoid
open Complex Set Filter Asymptotics
open scoped Topology
attribute [local irreducible] thetaA thetaSigma thetaZeta thetaEtaExpression

private theorem zeta_regular_part_at_zero {t : ℝ} (ht : 0<t) : zetaPoleRegular t 0=0 := by
  let u := sigmaDivZero t
  have even (z : ℂ) : u (-z)=u z := by
    by_cases zero : z=0
    · simp [zero]
    have e := mul_sigmaDivZero t (-z)
    rw [thetaSigma_neg,neg_mul,neg_inj] at e
    exact mul_left_cancel₀ zero (e.trans (mul_sigmaDivZero t z).symm)
  have d : HasDerivAt u (deriv u 0) 0 := (sigmaDivZero_differentiable ht (0:ℂ)).hasDerivAt
  have dneg : HasDerivAt u (deriv u 0) (-0) := by simpa only [neg_zero] using d
  have neg : HasDerivAt (fun z : ℂ => u (-z)) (-deriv u 0) 0 := by
    simpa only [neg_zero,mul_neg,mul_one,Function.comp_def,id_eq] using
      dneg.comp 0 (hasDerivAt_id (0:ℂ)).neg
  have eq : (fun z : ℂ => u (-z))=u := funext even
  rw [eq] at neg
  have z : deriv u 0=0 := by linear_combination (norm := ring_nf) neg.deriv/2
  change deriv u 0/u 0=0
  rw [z,zero_div]

/-- The literal isolated-singularity formula of §6.1. Its unit factor
is holomorphic with value one and satisfies the stated O(z) bound. -/
theorem thetaA_essential_factor {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0=1 ∧ (fun z => U z-1)=O[𝓝 (0:ℂ)] (fun z => z) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), thetaA t a z=z⁻¹^2*exp (2*((a:ℂ)-1)/z)*U z := by
  let L := rhombicPeriodPair t ht
  let k : ℂ := 2*((a:ℂ)-1)
  let s := thetaSigma t
  let d := sigmaDivZero t
  let v := fun z : ℂ => exp (k*zetaPoleRegular t z+2*thetaEtaExpression t*z)
  let U := fun z : ℂ => v z*(s (z-a)^2/(d z^2*s a^2))
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a<2)
  have na : s a≠0 := (thetaSigma_zero_iff_lattice_of_pos ht ht a).not.mpr haL
  have av : AnalyticAt ℂ v 0 := ((analyticAt_const.mul (zetaPoleRegular_analyticAt ht (Or.inr rfl))).add (analyticAt_const.mul analyticAt_id)).cexp
  have adj : AnalyticAt ℂ (fun z => s (z-a)) 0 := (thetaSigma_analyticAt ht _).comp (analyticAt_id.sub analyticAt_const)
  have nd : d 0≠0 := sigmaDivZero_ne_zero ht (Or.inr rfl)
  have au : AnalyticAt ℂ U 0 := av.mul ((adj.pow 2).div (((sigmaDivZero_differentiable ht).analyticAt 0 |>.pow 2).mul analyticAt_const) (mul_ne_zero (pow_ne_zero _ nd) (pow_ne_zero _ na)))
  have unit : U 0=1 := by
    dsimp [U,v,d,s] at *
    simp [zeta_regular_part_at_zero ht,sigmaDivZero_zero ht,thetaSigma_neg,na]
  refine ⟨U,au,unit,by simpa only [unit,sub_zero] using au.differentiableAt.isBigO_sub,?_⟩
  have avoid := latticePoleSet_punctured_avoids L (A := {0}) (finite_singleton _) (0:ℂ)
  filter_upwards [avoid,self_mem_nhdsWithin] with z h hz
  change z≠0 at hz
  have off : z∉L.lattice := fun e => h ⟨0,mem_singleton _,by simpa using e⟩
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht z haL off]
  unfold thetaSigmaKernel
  rw [thetaZeta_eq_inv_add_regular ht off,← mul_sigmaDivZero t z]
  change exp (k*(z⁻¹+zetaPoleRegular t z)+2*thetaEtaExpression t*z)*(s (z-a)^2/((z*d z)^2*s a^2))=
    z⁻¹^2*exp (k/z)*U z
  rw [show k*(z⁻¹+zetaPoleRegular t z)+2*thetaEtaExpression t*z=k/z+(k*zetaPoleRegular t z+2*thetaEtaExpression t*z) by ring,exp_add]
  dsimp only [U,v]
  ring

/-- For 0<a<1 the singularity is genuinely essential; at a=1 the
coefficient is the Weierstrass function minus its half-period value. -/
theorem thetaA_not_meromorphic_at_origin {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) :
    ¬ MeromorphicAt (thetaA t a) 0 := by
  obtain ⟨U,an,one,_,eq⟩ := thetaA_essential_factor ht ha
  let c : ℂ := 2*((a:ℂ)-1)
  have nz : c≠0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr (by exact_mod_cast ha.2.ne))
  intro hm
  apply exp_reciprocal_not_meromorphic nz
  have nu : U 0≠0 := one ▸ one_ne_zero
  have E := ((analyticAt_id.pow 2).meromorphicAt.mul hm).div an.meromorphicAt
  apply E.congr
  filter_upwards [eq,nhdsWithin_le_nhds (an.continuousAt.eventually_ne nu),self_mem_nhdsWithin] with z he hu hz
  change z≠0 at hz
  change z^2*thetaA t a z/U z=exp (c/z)
  rw [he]
  dsimp [c]
  field_simp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.thetaA_essential_factor
#print axioms TwoAxisHelicoid.thetaA_not_meromorphic_at_origin
