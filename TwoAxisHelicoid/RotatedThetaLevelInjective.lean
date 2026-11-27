import TwoAxisHelicoid.HorizontalCollisionGaussDirections
import TwoAxisHelicoid.PhysicalLevelThetaPhase
import TwoAxisHelicoid.TorusThetaDirection
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Omitting any one unoriented tangent direction suffices on a noncentral
physical level. The test uses the torus-periodic theta quotient after the
constant rotation appropriate to that physical height. -/
theorem height_level_injective_of_rotated_theta {t a h : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) (hn : h≠0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (C : ℂ) (avoid : ∀ z, z∉(rhombicPeriodPair t ht).lattice → X z 2=X 1 2+h →
      (C*torusThetaDirection t a z).re≠0) :
    let L := rhombicPeriodPair t ht
    let Y := fun u : PuncturedPeriodTorus L => periodTorusLift L X per u.1
    InjOn Y {u | Y u 2=X 1 2+h} := by
  intro L Y u hu v _ same
  by_contra distinct
  obtain ⟨z,ez⟩ := Quotient.exists_rep u.1
  obtain ⟨w,ew⟩ := Quotient.exists_rep v.1
  change periodTorusProjection L z=u.1 at ez
  change periodTorusProjection L w=v.1 at ew
  have oz : z∉L.lattice := fun m => u.2 (ez.symm.trans ((periodTorusProjection_eq_zero L z).mpr m))
  have ow : w∉L.lattice := fun m => v.2 (ew.symm.trans ((periodTorusProjection_eq_zero L w).mpr m))
  have neq : periodTorusProjection L z≠periodTorusProjection L w :=
    fun e => distinct (Subtype.ext (ez.symm.trans (e.trans ew)))
  have xu : X z=Y u := congrArg (periodTorusLift L X per) ez
  have xv : X w=Y v := congrArg (periodTorusLift L X per) ew
  have level : X z 2=X 1 2+h := (congrFun xu 2).trans hu
  obtain ⟨g,l,r,_,_,on,_,_,all⟩ := horizontal_collision_all_gauss_directions ht ha one_ne_zero d per oz ow neq
    (xu.trans (same.trans xv.symm)) (fun e => hn (by linarith))
  let E := exp (I*((2*(a-1)*h:ℝ):ℂ))
  obtain ⟨y,_,zero⟩ := all (conj (C/E))
  let z' := g y
  let H := actualComplexHeight t a 1 ht
  let b := Real.exp (-(2*(a-1))*(H z').im)*Real.exp (2*(1-a)*Real.pi/t*z'.re)
  have bp : 0<b := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have lev : X z' 2=X 1 2+h := (on y).2.trans level
  have hr : (H z').re=h := by
    rw [← actual_complex_height_centered_primitive ht d (on y).1,lev]
    ring
  have form := physical_level_gauss_theta_ratio ht ha root z'
  dsimp only at form
  change thetaGauss t a 1 z'=I*exp (I*((2*(a-1)*(H z').re:ℝ):ℂ))*
    (Real.exp (-(2*(a-1))*(H z').im):ℂ)*centralPhaseThetaRatio t a z' at form
  rw [hr,theta_ratio_torus_direction] at form
  have eq : (C/E)*thetaGauss t a 1 z'= I*((b:ℂ)*(C*torusThetaDirection t a z')) := by
    rw [form]
    dsimp only [E,b]
    push_cast
    field_simp [Complex.exp_ne_zero]
  change (conj (conj (C/E))*thetaGauss t a 1 z').im=0 at zero
  rw [show conj (conj (C/E))=C/E by simp] at zero
  rw [eq] at zero
  have reduced : b*(C*torusThetaDirection t a z').re=0 := by simpa [Complex.mul_im,Complex.mul_re] using zero
  exact avoid _ (on y).1 lev ((mul_eq_zero.mp reduced).resolve_left bp.ne')

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_level_injective_of_rotated_theta
