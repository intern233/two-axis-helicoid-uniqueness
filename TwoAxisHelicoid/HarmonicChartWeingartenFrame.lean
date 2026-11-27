import TwoAxisHelicoid.HarmonicChartUnitNormal
import TwoAxisHelicoid.WeingartenFrameConstruction

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology

/-- Differentiating the three orthonormality identities of the actual
normal supplies its full Weingarten frame. Symmetry comes from equality of
mixed partial derivatives; trace zero comes from the harmonic equation. -/
theorem harmonic_chart_weingarten_frame {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hreg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w)) :
    let A := planePartial 1 X
    let B := planePartial I X
    let N := harmonicChartNormal X
    let nx := planePartial 1 N z
    let ny := planePartial I N z
    ConformalNormalFrame (A z) (B z) (N z) nx ny (A z ⬝ᵥ A z) (-(nx ⬝ᵥ A z)) (-(nx ⬝ᵥ B z)) := by
  let A := planePartial 1 X
  let B := planePartial I X
  let N := harmonicChartNormal X
  have hX : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hreg.self_of_nhds.1 j))
  have hA : AnalyticAt ℝ A z := planePartial_analyticAt hX 1
  have hB : AnalyticAt ℝ B z := planePartial_analyticAt hX I
  have hdatum := hreg.mono fun w hw => harmonicChartNormal_data
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hw.1 j)) hw.2.1 hw.2.2
  obtain ⟨ha,hpos,hmetric,hab,_,hn,hna,hnb⟩ := hdatum.self_of_nhds
  have hN : DifferentiableAt ℝ N z := ha.differentiableAt
  have h1 (v : ℂ) : N z ⬝ᵥ planePartial v N z = 0 := by
    have h := derivative_of_constant_pairing hN hN (c := 1) (hdatum.mono fun _ h => h.2.2.2.2.2.1) v
    rw [dotProduct_comm (planePartial v N z) _] at h
    linarith
  have h2 (v : ℂ) := derivative_of_constant_pairing (X := N) (Y := A) hN hA.differentiableAt
    (c := 0) (hdatum.mono fun _ h => h.2.2.2.2.2.2.1) v
  have h3 (v : ℂ) := derivative_of_constant_pairing (X := N) (Y := B) hN hB.differentiableAt
    (c := 0) (hdatum.mono fun _ h => h.2.2.2.2.2.2.2) v
  have hm : planePartial I A z = planePartial 1 B z := planePartial_commute hX I 1
  have ht : planePartial 1 A z + planePartial I B z = 0 :=
    (laplacian_plane_partials hX).symm.trans (harmonic_coordinate_laplacian_zero hreg.self_of_nhds.1)
  have hny : planePartial I N z ⬝ᵥ A z = planePartial 1 N z ⬝ᵥ B z := by
    have p := h2 I
    have q := h3 1
    rw [hm] at p
    linarith
  have htr : planePartial I N z ⬝ᵥ B z = -(planePartial 1 N z ⬝ᵥ A z) := by
    have p := h2 1
    have q := h3 I
    have rel := congrArg (fun v => N z ⬝ᵥ v) ht
    rw [dotProduct_add,dotProduct_zero] at rel
    linarith
  exact weingarten_frame_of_pairings hpos rfl hmetric.symm hab hn hna hnb (h1 1) (h1 I)
    (neg_neg _).symm (neg_neg _).symm (hny.trans (neg_neg _).symm) htr

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_weingarten_frame
