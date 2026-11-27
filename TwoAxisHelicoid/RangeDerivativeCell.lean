import TwoAxisHelicoid.RangeDerivativeNode
import TwoAxisHelicoid.ThetaDerivativeHolomorphic
import TwoAxisHelicoid.QuadratureEnclosure
import TwoAxisHelicoid.RationalQuadrature12

namespace TwoAxisHelicoid
open ComplexBall Metric Set
attribute [local irreducible] thetaA thetaJet thetaAa thetaAtMidline

structure RangeDerivativeCell where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : RangeDerivativeTrace
  nodes : Fin 12 → RangeDerivativeNode
  outputA : DyadicBall
  outputT : DyadicBall

namespace RangeDerivativeCell

def boundA (s : RangeCertificateSetup) (w : RangeDerivativeCell) : ℚ :=
  (w.diskFunction.resultA.output.toBall s.config.prec).center.absUpper+
    (w.diskFunction.resultA.output.toBall s.config.prec).radius

def boundT (s : RangeCertificateSetup) (w : RangeDerivativeCell) : ℚ :=
  (w.diskFunction.resultT.output.toBall s.config.prec).center.absUpper+
    (w.diskFunction.resultT.output.toBall s.config.prec).radius

def Valid (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (x h R : ℚ) (w : RangeDerivativeCell) : Prop :=
  0 ≤ h ∧ h < R ∧
  (w.center.toBall s.config.prec).coarsens
    (horizontalCenterBall s.config (p.base.height.toBall s.config.prec) x) ∧
  (w.disk.toBall s.config.prec).coarsens ((w.center.toBall s.config.prec).inflate R) ∧
  w.diskFunction.Valid s p w.disk ∧
  (∀ i : Fin 12, (w.nodes i).Valid s p w.center h (rationalQuadrature12.node i) (rationalQuadrature12.weight i)) ∧
  (w.outputA.toBall s.config.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).weightedA.output.toBall s.config.prec))).inflate
      (quadratureErrorBound rationalQuadrature12 12 h R (w.boundA s))) ∧
  (w.outputT.toBall s.config.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).weightedT.output.toBall s.config.prec))).inflate
      (quadratureErrorBound rationalQuadrature12 12 h R (w.boundT s)))

instance (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (x h R : ℚ) (w : RangeDerivativeCell) :
    Decidable (w.Valid s p x h R) := by unfold Valid; infer_instance

theorem sound (s : RangeCertificateSetup) (hs : s.Valid) {t a : ℝ}
    (p : RangeDerivativeParameters) (hp : p.Encloses s t a)
    (x h R : ℚ) (w : RangeDerivativeCell) (hw : w.Valid s p x h R) :
    (w.outputA.toBall s.config.prec).Contains
      (normalizedIntegral (thetaAa t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    (w.outputT.toBall s.config.prec).Contains
      (normalizedIntegral (thetaAtMidline t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    DiffContOnCl ℂ (thetaAa t a) (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) ∧
    DiffContOnCl ℂ (thetaAtMidline t a) (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) := by
  rcases hw with ⟨hh0,hhR,hcenter,hdisk,hdf,hnodes,houtA,houtT⟩
  have he := hp
  have htpos : 0 < t := lt_of_lt_of_le (s.lower_pos hs) he.height_lower
  have hbt := hp.height
  have hcenter' := coarsen_contains (horizontalCenterBall_contains hbt s.config x) hcenter
  let c : ℂ := (x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)
  have hbound : ∀ z ∈ closedBall c (R : ℝ),
      z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t ∧
      ‖thetaAa t a z‖ ≤ ((w.boundA s) : ℝ) ∧ ‖thetaAtMidline t a z‖ ≤ ((w.boundT s) : ℝ) := by
    intro z hz
    have hdz := coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk
    have hf := w.diskFunction.sound s hs p he hdz hdf
    exact ⟨hf.2.2.1,hf.2.2.2,norm_le hf.1,norm_le hf.2.1⟩
  let S : Set ℂ := {z | z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t}
  have hA : DifferentiableOn ℂ (thetaAa t a) S := fun z hz =>
    (thetaAa_differentiableAt htpos a hz.1 hz.2).differentiableWithinAt
  have hT : DifferentiableOn ℂ (thetaAtMidline t a) S := fun z hz =>
    (thetaAtMidline_differentiableAt htpos a hz.1 hz.2).differentiableWithinAt
  have hanA := hA.diffContOnCl_ball (fun z hz => ⟨(hbound z hz).1,(hbound z hz).2.1⟩)
  have hanT := hT.diffContOnCl_ball (fun z hz => ⟨(hbound z hz).1,(hbound z hz).2.1⟩)
  have hnode (i : Fin 12) := (w.nodes i).sound s hs p he w.center hcenter' h
    (rationalQuadrature12.node i) (rationalQuadrature12.weight i) (hnodes i)
  exact ⟨quadrature_enclosure rationalQuadrature12_exact rationalQuadrature12_nodes hh0 hhR
      hanA (fun z hz => (hbound z hz).2.2.1) (fun i => (hnode i).1) houtA,
    quadrature_enclosure rationalQuadrature12_exact rationalQuadrature12_nodes hh0 hhR
      hanT (fun z hz => (hbound z hz).2.2.2) (fun i => (hnode i).2) houtT,hanA,hanT⟩

end RangeDerivativeCell
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RangeDerivativeCell.sound
