import TwoAxisHelicoid.RegularHorizontalFiberTangent
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- A spatial double point off the central level forces every
projective Gauss phase to occur on one single bounded open arc of
that horizontal fiber. In particular an open semicircle of permitted
phases suffices for injectivity on the entire level. -/
theorem horizontal_collision_all_gauss_directions {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z)
    {z w : ℂ} (oz : z∉(rhombicPeriodPair t ht).lattice) (ow : w∉(rhombicPeriodPair t ht).lattice)
    (distinct : periodTorusProjection (rhombicPeriodPair t ht) z≠periodTorusProjection (rhombicPeriodPair t ht) w)
    (collision : X z=X w) (noncentral : X z 2≠X 1 2) :
    let L := rhombicPeriodPair t ht
    let G := thetaGauss t a 1
    ∃ (g : ℝ → ℂ) (u v : ℝ), u<v ∧ Continuous g ∧
      (∀ s : ℝ, g s∉L.lattice ∧ X (g s) 2=X z 2) ∧ X (g u)=X z ∧ X (g v)=X z ∧
      ∀ d : ℂ, ∃ s∈Ioo u v, (conj d*G (g s)).im=0 := by
  let L := rhombicPeriodPair t ht
  let h := X z 2-X 1 2
  let G := thetaGauss t a 1
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X period q.1
  have eql : X 1 2+h=X z 2 := by dsimp [h]; ring
  obtain ⟨g,s,q,cg,prop,_,ran⟩ := actual_regular_horizontal_fibers ht ha hc diff period (sub_ne_zero.mpr noncentral)
  have image (t : ℝ) : Y (q t)=X (g t) := congrArg (periodTorusLift L X period) (prop t).2.2
  have lev (t : ℝ) : X (g t) 2=X z 2 := by
    have hq := mem_range_self (f := q) t
    rw [ran] at hq
    exact (congrFun (image t).symm 2).trans (hq.trans eql)
  let lift := fun (p : ℂ) (hp : p∉L.lattice) =>
    (⟨periodTorusProjection L p,fun eq => hp ((periodTorusProjection_eq_zero L p).mp eq)⟩ : PuncturedPeriodTorus L)
  have get (p : ℂ) (hp : p∉L.lattice) (same : X p=X z) : ∃ t, q t=lift p hp := by
    change lift p hp∈range q
    rw [ran]
    exact (congrFun same 2).trans eql.symm
  obtain ⟨u,eu⟩ := get z oz rfl
  obtain ⟨v,ev⟩ := get w ow collision.symm
  have ne : u≠v := fun e => distinct (congrArg Subtype.val (eu.symm.trans ((congrArg q e).trans ev)))
  have xu : X (g u)=X z := (image u).symm.trans (congrArg Y eu)
  have xv : X (g v)=X z := (image v).symm.trans ((congrArg Y ev).trans collision.symm)
  have endpoints : ∃ i j : ℝ,i<j ∧ X (g i)=X z ∧ X (g j)=X z := by
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact ⟨u,v,lt,xu,xv⟩
    · exact ⟨v,u,gt,xv,xu⟩
  obtain ⟨i,j,lt,xi,xj⟩ := endpoints
  refine ⟨g,i,j,lt,cg,fun t => ⟨(prop t).1,lev t⟩,xi,xj,?_⟩
  intro d
  let l := fun t => d.re*X (g t) 0+d.im*X (g t) 1
  let k := fun t => ((normSq (G (g t)))⁻¹+1)/2
  have deriv (y : ℝ) : HasDerivAt l (k y*(conj d*G (g y)).im) y := by
    have tan := (actual_regular_horizontal_fiber_tangent ht ha hc diff period cg (fun r => (prop r).2.1)
      (prop y).1 (fun eq => noncentral ((lev y).symm.trans eq))).2
    have a := ((ContinuousLinearMap.proj (0:Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt y tan).const_mul d.re
    have b := ((ContinuousLinearMap.proj (1:Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt y tan).const_mul d.im
    have e := a.add b
    change HasDerivAt l (d.re*(k y*(G (g y)).im)+d.im*(-k y*(G (g y)).re)) y at e
    convert e using 1
    simp only [Complex.mul_im,Complex.conj_re,Complex.conj_im]
    ring
  have same : l i=l j := by dsimp [l]; rw [xi,xj]
  obtain ⟨y,hy,zero⟩ := exists_hasDerivAt_eq_zero lt (fun t _ => (deriv t).continuousAt.continuousWithinAt)
    same (fun t _ => deriv t)
  have positive : 0<k y := div_pos (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (normSq_nonneg _)) one_pos) (by norm_num)
  exact ⟨y,hy,(mul_eq_zero.mp zero).resolve_left positive.ne'⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_collision_all_gauss_directions
