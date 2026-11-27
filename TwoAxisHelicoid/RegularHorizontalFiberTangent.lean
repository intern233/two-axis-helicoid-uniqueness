import TwoAxisHelicoid.RegularHorizontalFibers
import TwoAxisHelicoid.GaussLevelTangent
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- A continuous lift of a vertical line through a holomorphic
coordinate with nonzero derivative is differentiable in its actual
imaginary coordinate; its speed is i divided by that derivative. -/
theorem vertical_complex_coordinate_lift_derivative {H : ℂ → ℂ} {g : ℝ → ℂ} {s y : ℝ} {d : ℂ}
    (hd : HasDerivAt H d (g y)) (nz : d≠0) (cont : ContinuousAt g y)
    (coord : ∀ x, H (g x)=⟨s,x⟩) : HasDerivAt g (I/d) y := by
  let line := fun x : ℝ => (⟨s,x⟩:ℂ)
  have eq : line=(fun x : ℝ => (s:ℂ)+x • I) := by
    funext x
    apply Complex.ext <;> simp [line,real_smul]
  have dl : HasDerivAt line I y := by
    rw [eq]
    simpa only [id_eq,one_smul] using! ((hasDerivAt_id y).smul_const I).const_add (s:ℂ)
  let A := (ContinuousLinearMap.toSpanSingleton ℂ d⁻¹).restrictScalars ℝ
  have result := (hd.hasFDerivAt.restrictScalars ℝ).of_comp_of_leftInverse cont dl.hasFDerivAt
    (.of_forall coord) (f'symm := A) (fun v => by change (v*d)*d⁻¹=v; field_simp)
  have out := result.hasDerivAt
  change HasDerivAt g (((1:ℝ) • I)*d⁻¹) y at out
  simpa only [one_smul,div_eq_mul_inv] using out

/-- Off the central height, both the height coefficient and the Gauss
data are regular on the actual curve. -/
theorem actual_noncentral_height_regular {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z)
    {z : ℂ} (off : z∉(rhombicPeriodPair t ht).lattice) (height : X z 2≠X 1 2) :
    coordinateData t a c ht z 2≠0 ∧ z-a∉(rhombicPeriodPair t ht).lattice ∧ z+a∉(rhombicPeriodPair t ht).lattice := by
  have regular : fderiv ℝ (fun u => X u 2) z≠0 := by
    intro zero
    obtain ⟨p,hp,_,_,same⟩ := actual_height_saddle_axis_representative ht ha hc diff period off zero
    exact height ((congrFun same 2).trans (actual_primitive_horizontal_line ht diff hp).2)
  have avoid := mt (actual_height_critical_iff ht ha hc diff off).mpr regular
  refine ⟨?_,fun e => avoid (Or.inl e),fun e => avoid (Or.inr e)⟩
  intro zero
  apply regular
  rw [(actual_coordinate_primitive_component ht diff off 2).fderiv,zero]
  ext v
  simp

/-- The global horizontal height parameter of the actual immersion
has the Weierstrass tangent dictated by its Gauss phase. -/
theorem actual_regular_horizontal_fiber_tangent {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z)
    {g : ℝ → ℂ} (cont : Continuous g) {s : ℝ}
    (coord : ∀ x, actualComplexHeight t a c ht (g x)=⟨s,x⟩)
    {y : ℝ} (off : g y∉(rhombicPeriodPair t ht).lattice) (height : X (g y) 2≠X 1 2) :
    let aG := thetaGauss t a 1 (g y)
    let k := ((normSq aG)⁻¹+1)/2
    HasDerivAt g (I/(coordinateData t a c ht (g y) 2)) y ∧
      HasDerivAt (X ∘ g) ![k*aG.im,-k*aG.re,0] y := by
  obtain ⟨nz,nm,np⟩ := actual_noncentral_height_regular ht ha hc diff period off height
  have dg := vertical_complex_coordinate_lift_derivative (actualComplexHeight_hasDerivAt ht off) nz
    cont.continuousAt coord
  have dX : HasDerivAt (X ∘ g) (levelTangent (coordinateData t a c ht (g y))) y :=
    (diff _ off).comp_hasDerivAt y dg
  have form := coordinateData_eq_original (c := c) ht ha off nm np
  have typed : coordinateData t a c ht (g y)=weierstrassTriple (thetaGauss t a 1 (g y))
      (coordinateData t a c ht (g y) 2) := form
  have eq := (congrArg levelTangent typed).trans (levelTangent_weierstrass (g := thetaGauss t a 1 (g y)) nz)
  rw [eq] at dX
  exact ⟨dg,dX⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_regular_horizontal_fiber_tangent
