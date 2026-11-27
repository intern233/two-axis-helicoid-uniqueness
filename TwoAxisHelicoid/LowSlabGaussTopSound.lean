import TwoAxisHelicoid.LowSlabGaussTopData
import TwoAxisHelicoid.LowSlabEdgeSound

namespace TwoAxisHelicoid
open Complex Set ComplexBall

theorem CheckedLowSlabGaussTop.sound {l r : ℚ} (cert : CheckedLowSlabGaussTop l r) :
    let p := certifiedClosedParameters
    ∀ x∈Icc (l:ℝ) r, (thetaGauss p.t p.a 1 ⟨x,3/8⟩).re<0 := by
  intro p
  have strip : (3/8:ℝ)∈Ioo 0 p.t := ⟨by norm_num,
    (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1⟩
  induction cert with
  | cell w ok =>
    intro x hx
    obtain ⟨valid,box,margin⟩ := ok
    have b := w.sound valid (coarsen_contains (low_slab_edge_contains hx) box) (by
      change (centralBandEdgePoint false ((3/8:ℚ):ℝ) x).im∈Ioo 0 p.t
      simpa [centralBandEdgePoint] using strip)
    have result := (re_bounds b).2.trans_lt (Rat.cast_lt.mpr margin)
    norm_num [centralBandEdgePoint] at result
    linarith
  | @join l m r _ _ first last =>
    intro x hx
    rcases le_total x (m:ℝ) with le|le
    · exact first x ⟨hx.1,le⟩
    · exact last x ⟨le,hx.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedLowSlabGaussTop.sound
