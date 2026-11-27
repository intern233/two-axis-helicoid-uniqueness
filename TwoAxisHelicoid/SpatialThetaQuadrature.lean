import TwoAxisHelicoid.SpatialRationalMeanCheck
import TwoAxisHelicoid.RationalQuadrature12
import TwoAxisHelicoid.SlopingFluxRootParameters
import TwoAxisHelicoid.CertifiedSaddleHeightBracket

namespace TwoAxisHelicoid
open Metric ComplexBall Set
attribute [local irreducible] thetaA

/-- Soundness on the actual certified parameters for a horizontal
segment at the specified real and imaginary coordinates. -/
theorem HorizontalRangeCell.certified_rational_mean {K N : ℕ} {rule : QuadratureRule K}
    (moments : rule.ExactTo N) (unit : rule.NodesInUnit) (c : QComplex) {h R : ℚ}
    (w : HorizontalRangeCell K) (check : w.validAtRational slopingFluxAnalyticSetup rule N
      TraceData.slopingFluxParams.interpret c h R) :
    let p := certifiedClosedParameters
    (w.output.toBall slopingFluxAnalyticSetup.config.prec).Contains
      (normalizedIntegral (thetaA p.t p.a) c.val (h:ℝ)) ∧
      DiffContOnCl ℂ (thetaA p.t p.a) (ball c.val (R:ℝ)) := by
  intro p
  let S := slopingFluxAnalyticSetup
  obtain ⟨lower,q,a,coeff,_⟩ := sloping_flux_root_parameter_enclosures
    (Ioo_subset_Icc_self certifiedClosedParameters_bounds.1) (Ioo_subset_Icc_self certifiedClosedParameters_bounds.2)
  rcases check with ⟨hp,hr,center,disk,fn,nodes,out⟩
  have cc : (w.center.toBall S.config.prec).Contains c.val :=
    coarsen_contains (show (ComplexBall.mk c 0).Contains c.val by simp [Contains]) center
  have bounds (z : ℂ) (hz : z∈closedBall c.val (R:ℝ)) :
      z∈thetaRegular p.t ∧ ‖thetaA p.t p.a z‖≤(w.diskBound S:ℝ) := by
    have inside := coarsen_contains (inflate_contains cc (mem_closedBall_iff_norm.mp hz)) disk
    have sound := w.diskFunction.horizontal_sound S slopingFluxAnalyticSetup_valid lower q a coeff inside fn
    exact ⟨sound.2,norm_le sound.1⟩
  have hol := (thetaA_differentiableOn p.height_pos p.a).diffContOnCl_ball (fun z hz => (bounds z hz).1)
  refine ⟨quadrature_enclosure moments unit hp hr hol (fun z hz => (bounds z hz).2) ?_ out,hol⟩
  exact fun i => (w.nodes i).sound S slopingFluxAnalyticSetup_valid TraceData.slopingFluxParams.interpret
    w.center lower q a coeff cc h (rule.node i) (rule.weight i) (nodes i)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HorizontalRangeCell.certified_rational_mean
