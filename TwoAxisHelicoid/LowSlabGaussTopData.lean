import TwoAxisHelicoid.CentralBandEdgeData

namespace TwoAxisHelicoid

def lowSlabGaussTopCheck (w : CentralGaussFieldTrace) (l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let b := w.result.output.toBall S.config.prec
  w.Valid ∧ (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall false (3/8) l r) ∧
    b.center.re+b.radius< -(1/1024:ℚ)

instance (w : CentralGaussFieldTrace) (l r : ℚ) : Decidable (lowSlabGaussTopCheck w l r) := by
  unfold lowSlabGaussTopCheck
  infer_instance

inductive CheckedLowSlabGaussTop : ℚ → ℚ → Prop
  | cell {l r} (w : CentralGaussFieldTrace) (check : lowSlabGaussTopCheck w l r) : CheckedLowSlabGaussTop l r
  | join {l m r} : CheckedLowSlabGaussTop l m → CheckedLowSlabGaussTop m r → CheckedLowSlabGaussTop l r

end TwoAxisHelicoid
