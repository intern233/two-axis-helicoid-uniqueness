import TwoAxisHelicoid.HarmonicChartWeingartenFrame
import TwoAxisHelicoid.MinimalNormalJacobiAlgebra

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology

/-- The harmonic-map equation of the actual oriented Gauss normal of a
regular conformal minimal chart, derived from orthogonality, unit length
and the harmonic coordinate equations. -/
theorem harmonic_chart_gauss_normal_equation {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hreg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w)) :
    let N := harmonicChartNormal X
    let nx := planePartial 1 N z
    let ny := planePartial I N z
    (Δ N) z + (nx ⬝ᵥ nx + ny ⬝ᵥ ny) • N z = 0 := by
  let A := planePartial 1 X
  let B := planePartial I X
  let N := harmonicChartNormal X
  let nx := planePartial 1 N z
  let ny := planePartial I N z
  have hX : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hreg.self_of_nhds.1 j)
  have hA := planePartial_analyticAt hX 1
  have hB := planePartial_analyticAt hX I
  have hdata := hreg.mono fun w hw => harmonicChartNormal_data
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hw.1 j)) hw.2.1 hw.2.2
  have hN : AnalyticAt ℝ N z := hdata.self_of_nhds.1
  have H := harmonic_chart_weingarten_frame hreg
  have h1 (v : ℂ) : planePartial v A z ⬝ᵥ A z = planePartial v B z ⬝ᵥ B z :=
    derivative_of_equal_squared_norms hA.differentiableAt hB.differentiableAt (hdata.mono fun _ h => h.2.2.1) v
  have h2 (v : ℂ) : planePartial v A z ⬝ᵥ B z + planePartial v B z ⬝ᵥ A z = 0 := by
    have he := derivative_of_constant_pairing (X := A) (Y := B) hA.differentiableAt hB.differentiableAt
      (c := 0) (hdata.mono fun _ h => h.2.2.2.1) v
    rwa [dotProduct_comm (planePartial v B z) _,add_comm] 
  have hcontract (v : ℂ) : planePartial v A z ⬝ᵥ nx + planePartial v B z ⬝ᵥ ny = 0 :=
    H.normal_column_contraction (h1 v) (h2 v)
  have hmix : planePartial I A z = planePartial 1 B z := planePartial_commute hX I 1
  have hca : planePartial 1 A z ⬝ᵥ nx + planePartial I A z ⬝ᵥ ny = 0 := hmix.symm ▸ hcontract 1
  have hcb : planePartial 1 B z ⬝ᵥ nx + planePartial I B z ⬝ᵥ ny = 0 := hmix ▸ hcontract I
  have hLA : (Δ A) z = 0 := harmonic_tangent_laplacian_zero hreg.self_of_nhds.1 1
  have hLB : (Δ B) z = 0 := harmonic_tangent_laplacian_zero hreg.self_of_nhds.1 I
  have ha : A z ⬝ᵥ (Δ N) z = 0 := by
    have hp := laplacian_of_constant_pairing (X := A) (Y := N) hA hN (c := 0)
      (hdata.mono fun _ h => (dotProduct_comm _ _).trans h.2.2.2.2.2.2.1)
    change A z ⬝ᵥ (Δ N) z + (Δ A) z ⬝ᵥ N z + 2*(planePartial 1 A z ⬝ᵥ nx+planePartial I A z ⬝ᵥ ny) = 0 at hp
    simpa only [hLA,zero_dotProduct,hca,mul_zero,add_zero] using hp
  have hb : B z ⬝ᵥ (Δ N) z = 0 := by
    have hp := laplacian_of_constant_pairing (X := B) (Y := N) hB hN (c := 0)
      (hdata.mono fun _ h => (dotProduct_comm _ _).trans h.2.2.2.2.2.2.2)
    change B z ⬝ᵥ (Δ N) z + (Δ B) z ⬝ᵥ N z + 2*(planePartial 1 B z ⬝ᵥ nx+planePartial I B z ⬝ᵥ ny) = 0 at hp
    simpa only [hLB,zero_dotProduct,hcb,mul_zero,add_zero] using hp
  have hn := laplacian_of_constant_pairing (X := N) (Y := N) hN hN (c := 1)
    (hdata.mono fun _ h => h.2.2.2.2.2.1)
  change N z ⬝ᵥ (Δ N) z + (Δ N) z ⬝ᵥ N z + 2*(nx ⬝ᵥ nx+ny ⬝ᵥ ny) = 0 at hn
  have hsym : (Δ N) z ⬝ᵥ N z = N z ⬝ᵥ (Δ N) z := dotProduct_comm _ _
  rw [hsym] at hn
  apply conformal_triple_orthogonal_zero H.metric_pos H.aa H.bb H.ab H.nn H.na H.nb
  · change A z ⬝ᵥ ((Δ N) z + (nx ⬝ᵥ nx+ny ⬝ᵥ ny) • N z) = 0
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul,ha,(dotProduct_comm (A z) (N z)).trans H.na,mul_zero,add_zero]
  · change B z ⬝ᵥ ((Δ N) z + (nx ⬝ᵥ nx+ny ⬝ᵥ ny) • N z) = 0
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul,hb,(dotProduct_comm (B z) (N z)).trans H.nb,mul_zero,add_zero]
  · simp only [dotProduct_add,dotProduct_smul,smul_eq_mul,H.nn,mul_one]
    linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_gauss_normal_equation
