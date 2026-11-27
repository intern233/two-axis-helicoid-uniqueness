import TwoAxisHelicoid.ActualComplexHeight
import TwoAxisHelicoid.AxisPrimitiveLines
import TwoAxisHelicoid.NullGaussDivisor
import TwoAxisHelicoid.HolomorphicSaddleCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

private theorem real_height_derivative_zero_iff (p : ℂ) : realCoefficientDerivative p=0 ↔ p=0 := by
  constructor
  · intro h
    have r := congrArg (fun D : ℂ →L[ℝ] ℝ => D 1) h
    have i := congrArg (fun D : ℂ →L[ℝ] ℝ => D I) h
    apply Complex.ext
    · simpa using r
    · simpa using i
  · rintro rfl
    ext w
    simp

/-- Height-critical points of the genuine immersion are precisely the
two marked divisor points, modulo periods. -/
theorem actual_height_critical_iff {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) :
    fderiv ℝ (fun w => X w 2) z=0 ↔
      z-a∈(rhombicPeriodPair t ht).lattice ∨ z+a∈(rhombicPeriodPair t ht).lattice := by
  have an := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  rw [(actual_coordinate_primitive_component ht hX hz 2).fderiv,real_height_derivative_zero_iff]
  change I*(c:ℂ)*(_-_)=0 ↔ _
  rw [mul_eq_zero,or_iff_right (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)),sub_eq_zero]
  exact rhombic_weierstrassP_eq_iff ht an hz

/-- At either actual critical point there are mutually inverse
holomorphic coordinates in which the height has the real Morse normal
form x²−y². The statement includes all period translates. -/
theorem actual_height_saddle_coordinates {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) (crit : fderiv ℝ (fun w => X w 2) z=0) :
    ∃ φ ψ : ℂ → ℂ, AnalyticAt ℂ φ z ∧ AnalyticAt ℂ ψ 0 ∧ φ z=0 ∧ ψ 0=z ∧
      (∀ᶠ w in 𝓝 z, ψ (φ w)=w) ∧ (∀ᶠ u in 𝓝 (0:ℂ), φ (ψ u)=u) ∧
      ∀ᶠ u in 𝓝 (0:ℂ), X (ψ u) 2=X z 2+u.re^2-u.im^2 := by
  let L := rhombicPeriodPair t ht
  let F := actualComplexHeight t a c ht
  let p := coordinateData t a c ht
  have near : ∀ᶠ w in 𝓝 z, w∉L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have d : ∀ w∉L.lattice, HasDerivAt F (p w 2) w := fun _ hn => actualComplexHeight_hasDerivAt ht hn
  have an : AnalyticAt ℂ F z := analyticAt_iff_eventually_differentiableAt.mpr (near.mono fun w hw => (d w hw).differentiableAt)
  have dd : deriv F =ᶠ[𝓝 z] fun w => p w 2 := near.mono fun w hw => (d w hw).deriv
  have first : deriv F z=0 := dd.self_of_nhds.trans ((real_height_derivative_zero_iff _).mp ((actual_coordinate_primitive_component ht hX hz 2).fderiv.symm.trans crit))
  have two : ((a:ℂ)+(a:ℂ)) ∉ L.lattice := by
    simpa only [Complex.ofReal_add] using real_not_mem_rhombic_lattice_of_pos ht
      (show 0<a+a by linarith [ha.1]) (show a+a<2 by linarith [ha.2])
  have regs : L.derivWeierstrassP z≠0 := by
    apply (rhombic_weierstrassP_critical_iff_of_pos ht ht hz).not.mpr
    intro h
    rcases (actual_height_critical_iff ht ha hc hX hz).mp crit with plus | minus
    · exact two (by convert L.lattice.sub_mem h (L.lattice.add_mem plus plus) using 1; ring)
    · exact two (by convert L.lattice.sub_mem (L.lattice.add_mem minus minus) h using 1; ring)
  have dp : HasDerivAt (fun w => p w 2) (I*(c:ℂ)*L.derivWeierstrassP z) z :=
    null_height_hasDerivAt (a := a) (p := p) (K := I*(c:ℂ)) ht (fun _ _ => rfl) hz
  have second : deriv (deriv F) z ≠0 := by
    rw [dd.deriv_eq,dp.deriv]
    exact mul_ne_zero (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) regs
  obtain ⟨φ,ψ,hφ,hψ,fc,pc,left,right,form⟩ := holomorphic_simple_critical_coordinate an first second
  obtain ⟨b,hb⟩ := actual_complex_height_real_primitive ht hX
  refine ⟨φ,ψ,hφ,hψ,fc,pc,left,right,?_⟩
  have inv : Tendsto ψ (𝓝 0) (𝓝 z) := pc ▸ hψ.continuousAt.tendsto
  filter_upwards [inv.eventually near,form] with u hu eq
  rw [hb _ hu,hb z hz]
  change (F (ψ u)).re+b=(F z).re+b+u.re^2-u.im^2
  rw [eq,Complex.add_re,pow_two,Complex.mul_re]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_critical_iff
#print axioms TwoAxisHelicoid.actual_height_saddle_coordinates
