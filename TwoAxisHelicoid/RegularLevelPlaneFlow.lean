import TwoAxisHelicoid.BoundedGlobalPlaneFlow
import TwoAxisHelicoid.RegularHeightCutoff
import TwoAxisHelicoid.RegularHeightTrajectoryOpen

namespace TwoAxisHelicoid
open Set Complex Filter Topology InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- On a possibly singular selected level, all critical points are fixed and
every regular orbit remains regular at all times. Its parametrization is
open in the actual level even when that level also contains a saddle. -/
theorem hamiltonian_flow_on_regular_part_of_level (L : PeriodPair) {h : ℂ → ℝ} (ch : Continuous h)
    (per : ∀ z w, w∈L.lattice → h (z+w)=h z) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, h z≠bad → ContDiffAt ℝ ∞ h z) :
    ∃ Φ : ℝ → ℂ → ℂ, (∀ z, Φ 0 z=z) ∧ (∀ a b z, Φ (a+b) z=Φ a (Φ b z)) ∧
      (∀ t z w, w∈L.lattice → Φ t (z+w)=Φ t z+w) ∧
      (∀ z, h z=v → (∀ w, fderiv ℝ h z w=0) → ∀ t, Φ t z=z) ∧
      ∀ z, h z=v → (∃ w, fderiv ℝ h z w≠0) → ∃ level : ∀ t, h (Φ t z)=v,
        ContDiff ℝ 1 (fun t => Φ t z) ∧ (∀ t, deriv (fun r => Φ r z) t≠0) ∧
        (∀ t, HasDerivAt (fun r => Φ r z) (I*gradient h (Φ t z)) t) ∧
        IsOpenMap (fun t => (⟨Φ t z,level t⟩ : h ⁻¹' {v})) := by
  obtain ⟨f,sf,pf,near⟩ := periodic_cutoff_near_selected_height L ch per distinct smooth
  let V := fun z => I*gradient f z
  have sg : ContDiff ℝ 1 (gradient f) := (toDual ℝ ℂ).symm.toContinuousLinearEquiv.contDiff.comp
    (sf.fderiv_right (by simp))
  have sv : ContDiff ℝ 1 V := contDiff_const.mul sg
  have vp (z w : ℂ) (hw : w∈L.lattice) : V (z+w)=V z := by
    have eq : (fun x => f (x+w))=f := funext fun x => pf x w hw
    have d := (fderiv_comp_add_right (𝕜:=ℝ) (f:=f) (x:=z) w).symm.trans (congrArg (fun g => fderiv ℝ g z) eq)
    exact congrArg (fun D => I*(toDual ℝ ℂ).symm D) d
  obtain ⟨Φ,start,add,ode,pΦ,stationary⟩ := periodic_plane_field_global_flow L sv vp
  have fieldAt (z : ℂ) (hz : h z=v) : V z≠0 ↔ ∃ w, fderiv ℝ h z w≠0 := by
    have diff := (smooth z (fun same => distinct (hz.symm.trans same))).differentiableAt (by simp)
    have same := (near z hz).fderiv_eq (𝕜:=ℝ)
    rw [diff.hasFDerivAt.sub_const v |>.fderiv] at same
    constructor
    · intro nonzero
      by_contra! all
      have h0 : fderiv ℝ h z=0 := ContinuousLinearMap.ext (fun w => all w)
      apply nonzero
      change I*(toDual ℝ ℂ).symm (fderiv ℝ f z)=0
      rw [same,h0,map_zero,mul_zero]
    · rintro ⟨w,nonzero⟩ zero
      have grad0 : gradient f z=0 := (mul_eq_zero.mp zero).resolve_left I_ne_zero
      apply nonzero
      rw [← same,← inner_gradient_left,grad0,inner_zero_left]
  refine ⟨Φ,start,add,pΦ,?_,?_⟩
  · intro z hz crit
    apply stationary
    by_contra nz
    obtain ⟨w,witness⟩ := (fieldAt z hz).mp nz
    exact witness (crit w)
  intro z hz initial
  let γ := fun t => Φ t z
  have cg : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (ode z t).continuousAt)
  have level := connected_orbit_preserves_selected_height ch cg (by simpa [γ,start] using hz)
    near (rotated_gradient_preserves_height (sf.differentiable (by simp)) (ode z))
  have derivs : deriv γ=V ∘ γ := funext fun t => (ode z t).deriv
  have sc : ContDiff ℝ 1 γ := contDiff_one_iff_deriv.mpr ⟨fun t => (ode z t).differentiableAt,
    derivs ▸ sv.continuous.comp cg⟩
  have regular (t : ℝ) := smooth (γ t) (by rw [level]; exact distinct)
  have nz (t : ℝ) : V (γ t)≠0 := by
    intro zero
    have back : Φ (-t) (Φ t z)=z := by rw [← add,neg_add_cancel,start]
    have eq : z=γ t := back.symm.trans (stationary _ zero (-t))
    exact (fieldAt z hz).mpr initial ((congrArg V eq).trans zero)
  have moving (t : ℝ) : deriv γ t≠0 := by rw [derivs]; exact nz t
  have physical (t : ℝ) : HasDerivAt γ (I*gradient h (γ t)) t := by
    have same := (near (γ t) (level t)).fderiv_eq (𝕜:=ℝ)
    rw [((regular t).differentiableAt (by simp)).hasFDerivAt.sub_const v |>.fderiv] at same
    have gradients : gradient f (γ t)=gradient h (γ t) := congrArg (fun D => (toDual ℝ ℂ).symm D) same
    simpa only [V,gradients] using (show HasDerivAt γ (V (γ t)) t from ode z t)
  exact ⟨level,sc,moving,physical,regular_height_trajectory_isOpenMap sc level
    (fun t => ⟨regular t,(fieldAt _ (level t)).mp (nz t)⟩) moving⟩

theorem periodic_flow_on_regular_part_of_level (L : PeriodPair) {h : ℂ → ℝ} (ch : Continuous h)
    (per : ∀ z w, w∈L.lattice → h (z+w)=h z) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, h z≠bad → ContDiffAt ℝ ∞ h z) :
    ∃ Φ : ℝ → ℂ → ℂ, (∀ z, Φ 0 z=z) ∧ (∀ a b z, Φ (a+b) z=Φ a (Φ b z)) ∧
      (∀ t z w, w∈L.lattice → Φ t (z+w)=Φ t z+w) ∧
      (∀ z, h z=v → (∀ w, fderiv ℝ h z w=0) → ∀ t, Φ t z=z) ∧
      ∀ z, h z=v → (∃ w, fderiv ℝ h z w≠0) → ∃ level : ∀ t, h (Φ t z)=v,
        ContDiff ℝ 1 (fun t => Φ t z) ∧ (∀ t, deriv (fun r => Φ r z) t≠0) ∧
        IsOpenMap (fun t => (⟨Φ t z,level t⟩ : h ⁻¹' {v})) := by
  obtain ⟨Φ,start,add,shift,fixed,orbits⟩ := hamiltonian_flow_on_regular_part_of_level L ch per distinct smooth
  refine ⟨Φ,start,add,shift,fixed,?_⟩
  intro z hz regular
  obtain ⟨level,sc,speed,_,op⟩ := orbits z hz regular
  exact ⟨level,sc,speed,op⟩

/-- A periodic height, smooth except possibly over the filled point's
height, admits a complete periodic tangent flow open on each regular
fiber at a different height. Regularity supplies the nonvanishing speed. -/
theorem regular_periodic_level_complete_flow (L : PeriodPair) {h : ℂ → ℝ} (ch : Continuous h)
    (per : ∀ z w, w∈L.lattice → h (z+w)=h z) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, h z≠bad → ContDiffAt ℝ ∞ h z)
    (reg : ∀ z, h z=v → ∃ w, fderiv ℝ h z w≠0) :
    ∃ Φ : ℝ → ℂ → ℂ, (∀ z, Φ 0 z=z) ∧ (∀ a b z, Φ (a+b) z=Φ a (Φ b z)) ∧
      (∀ t z w, w∈L.lattice → Φ t (z+w)=Φ t z+w) ∧
      ∀ z, h z=v → ∃ level : ∀ t, h (Φ t z)=v,
        ContDiff ℝ 1 (fun t => Φ t z) ∧ (∀ t, deriv (fun r => Φ r z) t≠0) ∧
        IsOpenMap (fun t => (⟨Φ t z,level t⟩ : h ⁻¹' {v})) := by
  obtain ⟨Φ,start,add,perΦ,_,orbits⟩ := periodic_flow_on_regular_part_of_level L ch per distinct smooth
  exact ⟨Φ,start,add,perΦ,fun z hz => orbits z hz (reg z hz)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_flow_on_regular_part_of_level
#print axioms TwoAxisHelicoid.regular_periodic_level_complete_flow

#print axioms TwoAxisHelicoid.hamiltonian_flow_on_regular_part_of_level
