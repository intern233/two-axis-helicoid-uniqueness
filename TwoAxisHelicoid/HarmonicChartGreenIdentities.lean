import TwoAxisHelicoid.RectangularGreenFlux
import TwoAxisHelicoid.HarmonicChartJacobiOperator

namespace TwoAxisHelicoid
open Complex Set MeasureTheory InnerProductSpace Laplacian Matrix
open scoped Interval ContDiff Topology

/-- The product of the squared norm of the shape operator with the
conformal area factor, written using the two derivatives of the actual
oriented Gauss normal. -/
noncomputable def jacobiPotentialDensity (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℝ :=
  let N := harmonicChartNormal X
  planePartial 1 N z ⬝ᵥ planePartial 1 N z+planePartial I N z ⬝ᵥ planePartial I N z

theorem regular_jacobi_equation_density {X : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (inj : Function.Injective (fderiv ℝ X z)) (solution : conformalSurfaceJacobi X u z=0) :
    (Δ u) z+jacobiPotentialDensity X z*u z=0 := by
  have nz : planePartial 1 X z ⬝ᵥ planePartial 1 X z≠0 := fun zero =>
    one_ne_zero (inj ((dotProduct_self_eq_zero.mp zero).trans (map_zero (fderiv ℝ X z)).symm))
  change ((Δ u) z+jacobiPotentialDensity X z*u z)/(planePartial 1 X z ⬝ᵥ planePartial 1 X z)=0 at solution
  exact (div_eq_zero_iff.mp solution).resolve_right nz

/-- Appendix D.4 on every compact rectangle of a regular isothermal
chart. The two coordinate integrals of each outward flux include the
physical boundary arclength factor: it cancels the reciprocal factor
in the unit conormal derivative. The interior uses the actual induced
area density and squared-gradient and shape-operator terms. -/
theorem harmonic_chart_jacobi_green_identities (X : ℂ → Fin 3 → ℝ) (a b : ℝ×ℝ) (ordered : a≤b)
    {u v : ℂ → ℝ}
    (cu : ∀ q∈Icc a b, ContDiffAt ℝ 2 u (Complex.equivRealProdCLM.symm q))
    (cv : ∀ q∈Icc a b, ContDiffAt ℝ 2 v (Complex.equivRealProdCLM.symm q))
    (reg : ∀ q∈Icc a b, ∀ᶠ w in 𝓝 (Complex.equivRealProdCLM.symm q),
       (∀ j, HarmonicAt (fun x => X x j) w) ∧ ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w))
    (solU : ∀ q∈Icc a b, conformalSurfaceJacobi X u (Complex.equivRealProdCLM.symm q)=0)
    (solV : ∀ q∈Icc a b, conformalSurfaceJacobi X v (Complex.equivRealProdCLM.symm q)=0) :
    rectangleOutwardFlux a b (fun z => u z*planePartial 1 v z) (fun z => u z*planePartial I v z)-
      rectangleOutwardFlux a b (fun z => v z*planePartial 1 u z) (fun z => v z*planePartial I u z)=0 ∧
    (∫ q in Icc a b, let z := Complex.equivRealProdCLM.symm q
      let g := planePartial 1 X z ⬝ᵥ planePartial 1 X z
      ((planePartial 1 u z^2+planePartial I u z^2)/g-jacobiPotentialDensity X z/g*u z^2)*g)=
        rectangleOutwardFlux a b (fun z => u z*planePartial 1 u z) (fun z => u z*planePartial I u z) := by
  have eqU q hq := regular_jacobi_equation_density (reg q hq).self_of_nhds.2.2 (solU q hq)
  have eqV q hq := regular_jacobi_equation_density (reg q hq).self_of_nhds.2.2 (solV q hq)
  refine ⟨jacobi_green_rectangle_second a b ordered cu cv eqU eqV,?_⟩
  rw [← jacobi_green_rectangle_first a b ordered (fun q hq => (cu q hq).of_le (by norm_num)) cu eqU]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q hq
  have nz := (harmonic_chart_weingarten_frame (reg q hq)).metric_pos.ne'
  dsimp only
  field_simp [nz]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_chart_jacobi_green_identities
