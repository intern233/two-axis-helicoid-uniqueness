import TwoAxisHelicoid.RectangleEdgeShapeData
import TwoAxisHelicoid.CentralArcFourthTail
import TwoAxisHelicoid.FirstSpatialDiskTrace
import TwoAxisHelicoid.ThetaLogHigher

namespace TwoAxisHelicoid
open Complex Set ComplexBall

/-- A single disk contains the indicated rational coordinate rectangle. -/
theorem rectangle_center_disk_contains {a b l r : ℚ} {x y : ℝ}
    (hx : x∈Icc (a:ℝ) b) (hy : y∈Icc (l:ℝ) r) :
    (⟨⟨(a+b)/2,(l+r)/2⟩,(r-l+b-a)/2⟩:ComplexBall).Contains ((x:ℂ)+I*y) := by
  change ‖(x:ℂ)+I*y-(⟨(((a+b)/2:ℚ):ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ)‖≤(((r-l+b-a)/2:ℚ):ℝ)
  have n := Complex.norm_le_abs_re_add_abs_im ((x:ℂ)+I*y-(⟨(((a+b)/2:ℚ):ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ))
  simp only [sub_re,sub_im,add_re,add_im,ofReal_re,ofReal_im,I_mul_re,I_mul_im,neg_zero,add_zero,zero_add] at n
  push_cast at n ⊢
  have bx : |x-((a:ℝ)+b)/2|≤((b:ℝ)-a)/2 := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have by' : |y-((l:ℝ)+r)/2|≤((r:ℝ)-l)/2 := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  exact n.trans (by linarith)

theorem central_trace_tail {t : ℝ} (lower : (slopingFluxAnalyticSetup.lower:ℝ)≤t)
    (j : ℕ) (small : j≤4) (v : ℂ) (imBound : |v.im|≤1) :
    let S := slopingFluxAnalyticSetup
    ‖thetaJet t j v-thetaPartial t j S.terms v‖≤
      ((if j=4 then 268435456 else S.error : ℕ):ℝ)/(DyadicBall.denominator S.config.prec:ℝ) := by
  intro S
  interval_cases j
  · exact S.tail_bound_one slopingFluxAnalyticSetup_valid lower 0 v imBound
  · exact S.tail_bound_one slopingFluxAnalyticSetup_valid lower 1 v imBound
  · exact firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576 (DyadicThetaTail.valid_of_checks firstDiskTail_valid)
      (by norm_num) lower (by simpa only [Rat.cast_one] using imBound)
  · exact rectangleEdgeThirdTail.remainder_bound S.config (4/5) 1 3 5 1048576 (DyadicThetaTail.valid_of_checks rectangleEdgeThirdTail_valid)
      (by norm_num) lower (by simpa only [Rat.cast_one] using imBound)
  · exact centralArcFourthTail.remainder_bound S.config (4/5) 1 4 5 268435456 (DyadicThetaTail.valid_of_checks centralArcFourthTail_valid)
      (by norm_num) lower (by simpa only [Rat.cast_one] using imBound)

theorem central_trace_jet {t : ℝ} {v : ℂ} {q : DyadicBall} {seed : DyadicThetaSeed}
    (lower : (slopingFluxAnalyticSetup.lower:ℝ)≤t)
    (hq : (q.toBall slopingFluxAnalyticSetup.config.prec).Contains (exp (-Real.pi*t)))
    (hs : seed.Contains slopingFluxAnalyticSetup.config.prec v) (bound : |v.im|≤1)
    (j : ℕ) (hj : j≤4) (w : DyadicThetaTrace)
    (ok : w.Valid slopingFluxAnalyticSetup.config j slopingFluxAnalyticSetup.terms
      (if j=4 then 268435456 else slopingFluxAnalyticSetup.error) q seed) :
    (w.output.toBall slopingFluxAnalyticSetup.config.prec).Contains (thetaJet t j v) :=
  w.sound _ _ _ _ hq _ hs (central_trace_tail lower j hj v bound) ok

theorem central_trace_height_parameter {t : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) :
    (TraceData.slopingFluxParams.height.interpret.toBall slopingFluxAnalyticSetup.config.prec).Contains (t:ℂ) :=
  coarsen_contains (realInterval_contains ht.1 ht.2) firstDiskNumbers.2.2.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_trace_tail
