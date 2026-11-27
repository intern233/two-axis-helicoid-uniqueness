import TwoAxisHelicoid.HelicoidRelativeHorizontal

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix
open scoped Topology

/-- The rotating horizontal coordinate admits a nonzero continuous
transverse quotient at each regular point of either vertical boundary.
Its derivative in the direction of that boundary vanishes. -/
theorem rhombic_axis_relative_direction {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX)) (α b : ℝ) {n : ℤ} {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) (hx : z.re=n) :
    let P := fun w => helicoidRelativeHorizontal α b (X w)
    let Q := verticalTransverseDifference P n
    AnalyticAt ℝ P z ∧ P z=0 ∧ fderiv ℝ P z I=0 ∧ Q z≠0 ∧ ContinuousAt Q z ∧
      ∀ᶠ w in 𝓝 z, P w=((w.re-n:ℝ):ℂ)*Q w := by
  let L := rhombicPeriodPair t ht
  let H := fun w => spatialGraphProjection 0 1 (X w)
  let E := fun w => exp (-((α*(X w 2-b):ℝ):ℂ)*I)
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hX.harmonic _ hz j)
  have ah : AnalyticAt ℝ H z := ((spatialGraphProjection 0 1).analyticAt _).comp ax
  have ap : AnalyticAt ℝ P z := (helicoidRelativeHorizontal_analytic α b _).comp ax
  have ae : AnalyticAt ℝ E z := by
    have rh : AnalyticAt ℝ (fun w => α*(X w 2-b)) z := analyticAt_const.mul (((analyticAt_pi_iff.mp ax) 2).sub analyticAt_const)
    exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp ((((ofRealCLM.analyticAt _).comp rh).neg).mul analyticAt_const)
  have zero {w : ℂ} (hw : w ∉ L.lattice) (on : w.re=n) : H w=0 := by
    have h := (rhombic_physical_axes_preimages ht hX hi hw).1.mpr ⟨n,on⟩
    exact Complex.ext h.1 h.2
  have hreg : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have tl : Tendsto (fun s : ℝ => z+s • I) (𝓝 0) (𝓝 z) := by
    have c : Continuous (fun s : ℝ => z+s • I) := by fun_prop
    simpa using (c.continuousAt (x := 0)).tendsto
  have sz := vertical_axis_horizontal_derivatives ax (hX.conformal _ hz) (hX.immersion _ hz)
    ((tl.eventually hreg).mono fun s hs => zero hs (by simp [Complex.real_smul,hx]))
  have der (v : ℂ) : fderiv ℝ P z v = E z * fderiv ℝ H z v := by
    have d := (ae.differentiableAt.hasFDerivAt.mul ah.differentiableAt.hasFDerivAt).fderiv
    change fderiv ℝ P z = _ at d
    rw [zero hz hx,zero_smul,add_zero] at d
    exact congrArg (fun D : ℂ →L[ℝ] ℂ => D v) d
  have h0 : P z=0 := by change E z*H z=0; rw [zero hz hx,mul_zero]
  have dz : fderiv ℝ P z I=0 := by rw [der,sz.1,mul_zero]
  have qn : verticalTransverseDifference P n z≠0 := by
    rw [verticalTransverseDifference_on _ hx,der]
    exact mul_ne_zero (Complex.exp_ne_zero _) sz.2
  refine ⟨ap,h0,dz,qn,verticalTransverseDifference_continuousAt ap hx,?_⟩
  have foot : verticalParameterFoot n z=z := Complex.ext hx.symm rfl
  have tend : Tendsto (verticalParameterFoot n) (𝓝 z) (𝓝 z) := foot ▸ (continuous_verticalParameterFoot n).continuousAt (x := z)
  filter_upwards [tend.eventually hreg] with w hw
  have atfoot : P (verticalParameterFoot n w)=0 := by
    change E _ * H _=0
    rw [zero hw rfl,mul_zero]
  simpa only [atfoot,sub_zero] using verticalTransverseDifference_factor P n w

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_axis_relative_direction
