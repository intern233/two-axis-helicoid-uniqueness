import TwoAxisHelicoid.TorusActualLifts
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.RegularLevelPlaneFlow
import TwoAxisHelicoid.QuotientLevelOrbits
import Mathlib.Topology.LocalAtTarget

namespace TwoAxisHelicoid
open Set Complex Topology
open scoped Topology ContDiff

/-- A regular level of a real height on a marked torus is parametrized
component by component by circles. Each parametrization comes with a
regular plane traversal of the same component, with the full real time
line as parameter. Smoothness of the height is only needed away from
the exceptional level of the filled point. -/
theorem regular_torus_level_component_parametrization (L : PeriodPair)
    {H : PeriodTorus L → ℝ} (ch : Continuous H) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, H (periodTorusProjection L z)≠bad →
      ContDiffAt ℝ ∞ (H ∘ periodTorusProjection L) z)
    (reg : ∀ z, H (periodTorusProjection L z)=v →
      ∃ w, fderiv ℝ (H ∘ periodTorusProjection L) z w≠0)
    (x : H ⁻¹' {v}) :
    ∃ (e : OrientationCircle ≃ₜ connectedComponent x) (ξ : ℝ → ℂ),
      ContDiff ℝ 1 ξ ∧ (∀ t, deriv ξ t≠0) ∧
      ∀ t : ℝ, periodTorusProjection L (ξ t)=(e (t:OrientationCircle)).1.1 := by
  let π := periodTorusProjection L
  let h := H ∘ π
  let S := H ⁻¹' {v}
  have onto : Function.Surjective π := Quotient.mk_surjective
  have projCont : Continuous π := QuotientAddGroup.continuous_mk
  have per (z w : ℂ) (hw : w∈L.lattice) : h (z+w)=h z :=
    congrArg H (periodTorusProjection_add_lattice L z w hw)
  obtain ⟨Φ,start,add,shift,orbits⟩ :=
    regular_periodic_level_complete_flow L (ch.comp projCont) per distinct smooth reg
  let A := fun t => quotientFiberDescend π onto (π ∘ Φ t)
  have act (t : ℝ) (z : ℂ) : A t (π z)=π (Φ t z) := by
    apply quotientFiberDescend_apply
    intro u w eq
    have lat := (periodTorusProjection_eq_iff L u w).mp eq
    calc π (Φ t u)=π (Φ t u+(w-u)) := (periodTorusProjection_add_lattice L _ _ lat).symm
         _=π (Φ t (u+(w-u))) := congrArg π (shift t u _ lat).symm
         _=π (Φ t w) := by rw [show u+(w-u)=w by abel]
  have stays (t : ℝ) (p : S) : A t p.1∈S := by
    obtain ⟨z,hz⟩ := onto p.1
    obtain ⟨level,_⟩ := orbits z (show h z=v from (congrArg H hz).trans p.2)
    change H (A t p.1)=v
    rw [← hz,act]
    exact level t
  let G := fun t (p : S) => (⟨A t p.1,stays t p⟩:S)
  have val (t : ℝ) (p : S) (z : ℂ) (hz : π z=p.1) : (G t p).1=π (Φ t z) := by
    change A t p.1=_
    rw [← hz,act]
  have zero (p : S) : G 0 p=p := by
    obtain ⟨z,hz⟩ := onto p.1
    exact Subtype.ext ((val 0 p z hz).trans ((congrArg π (start z)).trans hz))
  have group (a b : ℝ) (p : S) : G (a+b) p=G a (G b p) := by
    obtain ⟨z,hz⟩ := onto p.1
    apply Subtype.ext
    rw [val _ _ _ hz,add,val a (G b p) (Φ b z) (val b p z hz).symm]
  have orbit (p : S) : Continuous (fun t => G t p) ∧ IsOpenMap (fun t => G t p) := by
    obtain ⟨z,hz⟩ := onto p.1
    obtain ⟨level,sc,_,op⟩ := orbits z (show h z=v from (congrArg H hz).trans p.2)
    let pr := S.restrictPreimage π
    let f := fun t => (⟨Φ t z,level t⟩ : h ⁻¹' {v})
    have eq : (fun t => G t p)=pr ∘ f := funext (fun t => Subtype.ext (val t p z hz))
    rw [eq]
    have cp : Continuous pr := (projCont.comp continuous_subtype_val).subtype_mk _
    exact ⟨cp.comp (sc.continuous.subtype_mk _),
      ((periodTorusProjection_isCoveringMap L).isOpenMap.restrictPreimage S).comp op⟩
  obtain ⟨z,hz⟩ := onto x.1
  obtain ⟨level,sc,nz,_⟩ := orbits z (show h z=v from (congrArg H hz).trans x.2)
  obtain ⟨d,dp,apart⟩ := nonzero_velocity_torus_period_gap L ((sc.differentiable one_ne_zero 0).hasDerivAt) (nz 0)
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_singleton.preimage ch).isCompact
  obtain ⟨T,tp,e,eq⟩ := compact_level_component_orbit_circle G zero group
    (fun p => (orbit p).1) (fun p => (orbit p).2) x ⟨d,dp,by
      intro r hr same
      apply apart r hr
      rw [start]
      change π (Φ r z)=π z
      rw [← val r x z hz,same,hz]⟩
  let ξ := fun t : ℝ => Φ (t*T) z
  refine ⟨e,ξ,sc.comp (contDiff_id.mul contDiff_const),?_,?_⟩
  · intro t
    have der := ((sc.differentiable one_ne_zero (t*T)).hasDerivAt).scomp t ((hasDerivAt_id' t).mul_const T)
    change deriv ((fun r => Φ r z) ∘ (fun s => s*T)) t≠0
    rw [der.deriv,one_mul]
    exact smul_ne_zero tp.ne' (nz (t*T))
  · intro t
    rw [eq]
    exact (val (t*T) x z hz).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_torus_level_component_parametrization
