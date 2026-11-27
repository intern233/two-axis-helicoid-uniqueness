import TwoAxisHelicoid.SinglePunctureEndFlux
import TwoAxisHelicoid.TorusFluxCurveIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory InnerProductSpace

/-- A square in lattice coordinates, traversed counterclockwise in those
coordinates. All endpoints and line segments belong to the punctured plane. -/
noncomputable def punctureSquareEdge (L : PeriodPair) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (x y u v : ℝ) (side : (x = u ∧ (x = -1/2 ∨ x = 1/2)) ∨ (y = v ∧ (y = -1/2 ∨ y = 1/2))) :
    PlanePolygon (L.lattice : Set ℂ)ᶜ ((r:ℂ)*spinSquareLinear L x y) ((r:ℂ)*spinSquareLinear L u v) := by
  apply PlanePolygon.step
  intro s _
  rw [AffineMap.lineMap_apply_module',Complex.real_smul]
  change (s:ℂ)*((r:ℂ)*spinSquareLinear L u v-(r:ℂ)*spinSquareLinear L x y)+(r:ℂ)*spinSquareLinear L x y ∉ L.lattice
  rw [show (s:ℂ)*((r:ℂ)*spinSquareLinear L u v-(r:ℂ)*spinSquareLinear L x y)+(r:ℂ)*spinSquareLinear L x y =
    (r:ℂ)*(spinSquareLinear L x y+(s:ℂ)*(spinSquareLinear L u v-spinSquareLinear L x y)) by ring]
  exact puncture_square_side_regular L x y u v s r hr hr' side

private noncomputable def fourSidePath {Ω : Set ℂ} {A B C D : ℂ}
    (bottom : PlanePolygon Ω A B) (right : PlanePolygon Ω B D)
    (top : PlanePolygon Ω C D) (left : PlanePolygon Ω A C) :
    Path (⟨A,bottom.source_mem⟩ : Ω) ⟨A,bottom.source_mem⟩ :=
  (bottom.pathIn.trans right.pathIn).trans (top.pathIn.symm.trans left.pathIn.symm)

private theorem fourSidePath_integral {Ω : Set ℂ} {A B C D : ℂ}
    (bottom : PlanePolygon Ω A B) (right : PlanePolygon Ω B D)
    (top : PlanePolygon Ω C D) (left : PlanePolygon Ω A C) {f : ℂ → ℂ} (hf : ContinuousOn f Ω) :
    curveIntegral (complexPlaneOneForm f) ((fourSidePath bottom right top left).map continuous_subtype_val) =
      bottom.integral f+right.integral f-top.integral f-left.integral f := by
  obtain ⟨hb,eb⟩ := bottom.curveIntegral_eq hf
  obtain ⟨hr,er⟩ := right.curveIntegral_eq hf
  obtain ⟨ht,et⟩ := top.curveIntegral_eq hf
  obtain ⟨hl,el⟩ := left.curveIntegral_eq hf
  simp only [fourSidePath,Path.map_trans,← Path.map_symm]
  rw [curveIntegral_trans (hb.trans hr) (ht.symm.trans hl.symm),curveIntegral_trans hb hr,
    curveIntegral_trans ht.symm hl.symm,curveIntegral_symm,curveIntegral_symm,eb,er,et,el]
  abel

private theorem punctureSquareEdge_integral (L : PeriodPair) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (x y u v : ℝ) (h) (f : ℂ → ℂ) :
    (punctureSquareEdge L hr hr' x y u v h).integral f =
      dilatedEdgeIntegral f (spinSquareLinear L x y) (spinSquareLinear L u v) r := by
  let A := spinSquareLinear L x y
  let B := spinSquareLinear L u v
  change ((r:ℂ)*B-(r:ℂ)*A)*(∫ s : ℝ in 0..1, f (AffineMap.lineMap (k := ℝ) ((r:ℂ)*A) ((r:ℂ)*B) s)) =
    ∫ s : ℝ in 0..1, (r:ℂ)*(B-A)*f ((r:ℂ)*(A+(s:ℂ)*(B-A)))
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change ((r:ℂ)*B-(r:ℂ)*A)*f (AffineMap.lineMap (k := ℝ) ((r:ℂ)*A) ((r:ℂ)*B) s) =
    (r:ℂ)*(B-A)*f ((r:ℂ)*(A+(s:ℂ)*(B-A)))
  rw [AffineMap.lineMap_apply_module',Complex.real_smul,
    show (s:ℂ)*((r:ℂ)*B-(r:ℂ)*A)+(r:ℂ)*A = (r:ℂ)*(A+(s:ℂ)*(B-A)) by ring,mul_sub (r:ℂ) B A]

noncomputable def punctureSquareLoop (L : PeriodPair) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (q : ↥((L.lattice : Set ℂ)ᶜ)) × Path q q :=
  let bot := punctureSquareEdge L hr hr' (-1/2) (-1/2) (1/2) (-1/2) (Or.inr ⟨rfl,Or.inl rfl⟩)
  let right := punctureSquareEdge L hr hr' (1/2) (-1/2) (1/2) (1/2) (Or.inl ⟨rfl,Or.inr rfl⟩)
  let top := punctureSquareEdge L hr hr' (-1/2) (1/2) (1/2) (1/2) (Or.inr ⟨rfl,Or.inr rfl⟩)
  let left := punctureSquareEdge L hr hr' (-1/2) (-1/2) (-1/2) (1/2) (Or.inl ⟨rfl,Or.inl rfl⟩)
  ⟨_,fourSidePath bot right top left⟩

/-- All coordinate fluxes vanish on this actual peripheral loop for every
size of its puncture-centered parallelogram. Its projection is a closed
path on the original punctured torus. -/
theorem punctureSquareLoop_all_coordinate_integrals_zero (L : PeriodPair)
    (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (j : Fin 3) :
    curveIntegral (complexPlaneOneForm (fun w => torusImmersionForms L X w j))
      ((punctureSquareLoop L hr hr').2.map continuous_subtype_val) = 0 := by
  have hcont : ContinuousOn (fun w => torusImmersionForms L X w j) (L.lattice : Set ℂ)ᶜ :=
    fun z hz => (scalarComplexCoefficient_analyticAt (hh z hz j)).continuousAt.continuousWithinAt
  simp only [punctureSquareLoop,fourSidePath_integral _ _ _ _ hcont,punctureSquareEdge_integral]
  exact actual_immersion_end_flux_zero L X hh hr hr' j

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctureSquareLoop_all_coordinate_integrals_zero
