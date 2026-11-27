import TwoAxisHelicoid.SinglePunctureEndFlux
import TwoAxisHelicoid.TorusSpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- A regular arc on one side of the lattice parallelogram enclosing the end. -/
noncomputable def punctureConormalArc (L : PeriodPair) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (x y u v : ℝ) (side : (x = u ∧ (x = -1/2 ∨ x = 1/2)) ∨ (y = v ∧ (y = -1/2 ∨ y = 1/2))) :
    ComplexPeriodArc (L.lattice : Set ℂ)ᶜ :=
  let A := spinSquareLinear L x y
  let B := spinSquareLinear L u v
  { left := 0
    right := 1
    ordered := zero_le_one
    curve := fun s => (r:ℂ)*(A+(s:ℂ)*(B-A))
    velocity := fun _ => (r:ℂ)*(B-A)
    continuous_curve := by fun_prop
    continuous_velocity := continuousOn_const
    stays := fun s _ => puncture_square_side_regular L x y u v s r hr hr' side
    derivative := fun s _ => by
      have hd := (((ofRealCLM.hasDerivAt (x := s)).mul_const (B-A)).const_add A).const_mul (r:ℂ)
      simpa using hd }

noncomputable def peripheralConormalFlux (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (j : Fin 3) : ℝ :=
  let pos := puncturedTorusPullback L X
  let edge := punctureConormalArc L hr hr'
  (edge (-1/2) (-1/2) (1/2) (-1/2) (Or.inr ⟨rfl,Or.inl rfl⟩)).spatialConormalFlux pos j+
    (edge (1/2) (-1/2) (1/2) (1/2) (Or.inl ⟨rfl,Or.inr rfl⟩)).spatialConormalFlux pos j-
    (edge (-1/2) (1/2) (1/2) (1/2) (Or.inr ⟨rfl,Or.inr rfl⟩)).spatialConormalFlux pos j-
    (edge (-1/2) (-1/2) (-1/2) (1/2) (Or.inl ⟨rfl,Or.inl rfl⟩)).spatialConormalFlux pos j

/-- The three components of the integral of the actual oriented spatial
unit conormal against Euclidean arclength vanish on the boundary of the
single puncture, independently of the handle periods. -/
theorem peripheral_spatial_flux_zero (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z)
    (hc : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (j : Fin 3) : peripheralConormalFlux L X hr hr' j = 0 := by
  obtain ⟨ha,hn,hD⟩ := torusImmersionForms_regular L X hh hc
  have flux (x y u v : ℝ) (h) :
      (punctureConormalArc L hr hr' x y u v h).spatialConormalFlux (puncturedTorusPullback L X) j =
        (dilatedEdgeIntegral (fun z => torusImmersionForms L X z j) (spinSquareLinear L x y)
          (spinSquareLinear L u v) r).im :=
    (punctureConormalArc L hr hr' x y u v h).spatialConormalFlux_eq_im _ (torusImmersionForms L X) hD hn j
      (fun z hz => (ha z hz j).continuousAt.continuousWithinAt)
  simp only [peripheralConormalFlux,flux]
  simpa only [punctureBoundaryIntegral,Complex.sub_im,Complex.add_im,Complex.zero_im] using
    congrArg im (actual_immersion_end_flux_zero L X hh hr hr' j)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.peripheral_spatial_flux_zero
