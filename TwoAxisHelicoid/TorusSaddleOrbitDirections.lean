import TwoAxisHelicoid.SaddleHamiltonianCoordinates
import TwoAxisHelicoid.SaddleOrbitTailDirections
import TwoAxisHelicoid.TorusMorseLevelGerms

namespace TwoAxisHelicoid
open Complex Filter Set Topology Function InnerProductSpace
open scoped Topology ContDiff

/-- The Hamiltonian equations and the sign of the coordinate Jacobian
hold eventually along a genuine plane orbit converging to a smooth
product saddle. The filter can describe either end of the orbit. -/
theorem hamiltonian_coordinates_on_convergent_tail {q : ℂ → ℝ×ℝ} {h : ℂ → ℝ}
    {z : ℂ} {c : ℝ} (smooth : ContDiffAt ℝ 1 q z) (inj : Injective (fderiv ℝ q z))
    (center : q z=0) (model : h =ᶠ[𝓝 z] fun y => c+(q y).1*(q y).2)
    {γ : ℝ → ℂ} (ode : ∀ t, HasDerivAt γ (I*gradient h (γ t)) t)
    {l : Filter ℝ} (lim : Tendsto γ l (𝓝 z)) :
    let u := Prod.fst ∘ q
    let v := Prod.snd ∘ q
    let J := saddleCoordinateJacobian u v
    Tendsto (u ∘ γ) l (𝓝 0) ∧ Tendsto (v ∘ γ) l (𝓝 0) ∧ J z≠0 ∧
      ∀ᶠ t in l, 0<J z*J (γ t) ∧
        HasDerivAt (u ∘ γ) ((-J (γ t))*u (γ t)) t ∧ HasDerivAt (v ∘ γ) (J (γ t)*v (γ t)) t := by
  let u := Prod.fst ∘ q
  let v := Prod.snd ∘ q
  let J := saddleCoordinateJacobian u v
  obtain ⟨nz,sign⟩ := saddle_coordinate_jacobian_fixed_sign smooth inj
  have at0 : Tendsto (q ∘ γ) l (𝓝 (0:ℝ×ℝ)) := center ▸ smooth.continuousAt.tendsto.comp lim
  refine ⟨continuous_fst.continuousAt.tendsto.comp at0,continuous_snd.continuousAt.tendsto.comp at0,nz,?_⟩
  filter_upwards [lim.eventually sign,lim.eventually (smooth.eventually (by simp)),lim.eventually model.eventuallyEq_nhds]
    with t same deriv localModel
  have du : DifferentiableAt ℝ u (γ t) := deriv.fst.differentiableAt one_ne_zero
  have dv : DifferentiableAt ℝ v (γ t) := deriv.snd.differentiableAt one_ne_zero
  obtain ⟨dx,dy⟩ := rotated_gradient_in_saddle_coordinates du dv localModel
  exact ⟨same,dx ▸ du.hasFDerivAt.comp_hasDerivAt t (ode t),dy ▸ dv.hasFDerivAt.comp_hasDerivAt t (ode t)⟩

/-- Although a homoclinic curve can approach two different lattice
lifts, the coordinate Jacobians there agree. Consequently one physical
end is on a horizontal arm and the other on a vertical arm. -/
theorem projected_homoclinic_ends_on_adjacent_axes (L : PeriodPair) {h : PeriodTorus L → ℝ}
    {p : PeriodTorus L} (e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ))
    (ez : e p=0) (model : ∀ᶠ q in 𝓝 p, h q=h p+(e q).1*(e q).2)
    {z : ℂ} (zp : periodTorusProjection L z=p) (smooth : ContDiffAt ℝ 1 (e ∘ periodTorusProjection L) z)
    (inj : Injective (fderiv ℝ (e ∘ periodTorusProjection L) z)) {γ : ℝ → ℂ}
    (ode : ∀ t, HasDerivAt γ (I*gradient (h ∘ periodTorusProjection L) (γ t)) t)
    {a b : ℂ} (ap : periodTorusProjection L a=p) (bp : periodTorusProjection L b=p)
    (left : Tendsto γ atBot (𝓝 a)) (right : Tendsto γ atTop (𝓝 b)) :
    let f := fun t => e (periodTorusProjection L (γ t))
    ((∀ᶠ t in atTop, (f t).2=0) ∧ ∀ᶠ t in atBot, (f t).1=0) ∨
      ((∀ᶠ t in atTop, (f t).1=0) ∧ ∀ᶠ t in atBot, (f t).2=0) := by
  let π := periodTorusProjection L
  let Q := e ∘ π
  let u := Prod.fst ∘ Q
  let v := Prod.snd ∘ Q
  let J := saddleCoordinateJacobian u v
  have cπ : Continuous π := QuotientAddGroup.continuous_mk
  have each {w : ℂ} (wp : π w=p) {l : Filter ℝ} (lim : Tendsto γ l (𝓝 w)) :
      Tendsto (u ∘ γ) l (𝓝 0) ∧ Tendsto (v ∘ γ) l (𝓝 0) ∧ J w≠0 ∧
        ∀ᶠ t in l, 0<J w*J (γ t) ∧ HasDerivAt (u ∘ γ) ((-J (γ t))*u (γ t)) t ∧
          HasDerivAt (v ∘ γ) (J (γ t)*v (γ t)) t := by
    have same := zp.trans wp.symm
    have dq := torus_lift_contDiffAt_of_same_projection L e same smooth
    have iq : Injective (fderiv ℝ Q w) := by
      change Injective (fderiv ℝ (e ∘ π) w)
      rw [← torus_height_derivative_eq_of_same_projection L e same]
      exact inj
    have ident : Q w=0 := (congrArg e wp).trans ez
    have approach : Tendsto π (𝓝 w) (𝓝 p) := wp ▸ cπ.continuousAt.tendsto
    exact hamiltonian_coordinates_on_convergent_tail dq iq ident (approach.eventually model) ode lim
  obtain ⟨ua,va,ja,neg⟩ := each ap left
  obtain ⟨ub,vb,_,pos⟩ := each bp right
  have same : π b=π a := bp.trans ap.symm
  have Ju : fderiv ℝ u b=fderiv ℝ u a := torus_height_derivative_eq_of_same_projection L (Prod.fst ∘ e) same
  have Jv : fderiv ℝ v b=fderiv ℝ v a := torus_height_derivative_eq_of_same_projection L (Prod.snd ∘ e) same
  have jac : J b=J a := by dsimp only [J,saddleCoordinateJacobian]; rw [Ju,Jv]
  rw [jac] at pos
  exact two_saddle_ends_on_different_axes (J:=J ∘ γ) ja ub ua vb va pos neg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.hamiltonian_coordinates_on_convergent_tail
#print axioms TwoAxisHelicoid.projected_homoclinic_ends_on_adjacent_axes
