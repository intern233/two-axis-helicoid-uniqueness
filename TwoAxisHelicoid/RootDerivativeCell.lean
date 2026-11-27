import TwoAxisHelicoid.RootDerivativeNode
import TwoAxisHelicoid.ThetaDerivativeHolomorphic
import TwoAxisHelicoid.QuadratureEnclosure
import TwoAxisHelicoid.RationalQuadrature12

namespace TwoAxisHelicoid
open ComplexBall Metric Set
attribute [local irreducible] thetaA thetaJet thetaAa thetaAtMidline

structure RootDerivativeCell where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : RootDerivativeTrace
  nodes : Fin 12 → RootDerivativeNode
  outputA : DyadicBall
  outputT : DyadicBall

namespace RootDerivativeCell

def boundA (w : RootDerivativeCell) : ℚ :=
  (w.diskFunction.resultA.output.toBall rootDyadicConfig.prec).center.absUpper+
    (w.diskFunction.resultA.output.toBall rootDyadicConfig.prec).radius

def boundT (w : RootDerivativeCell) : ℚ :=
  (w.diskFunction.resultT.output.toBall rootDyadicConfig.prec).center.absUpper+
    (w.diskFunction.resultT.output.toBall rootDyadicConfig.prec).radius

def Valid (p : RootDerivativeParameters) (x h R : ℚ) (w : RootDerivativeCell) : Prop :=
  0 ≤ h ∧ h < R ∧
  (w.center.toBall rootDyadicConfig.prec).coarsens
    (horizontalCenterBall rootDyadicConfig (p.base.height.toBall rootDyadicConfig.prec) x) ∧
  (w.disk.toBall rootDyadicConfig.prec).coarsens ((w.center.toBall rootDyadicConfig.prec).inflate R) ∧
  w.diskFunction.Valid p w.disk ∧
  (∀ i : Fin 12, (w.nodes i).Valid p w.center h (rationalQuadrature12.node i) (rationalQuadrature12.weight i)) ∧
  (w.outputA.toBall rootDyadicConfig.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).weightedA.output.toBall rootDyadicConfig.prec))).inflate
      (quadratureErrorBound rationalQuadrature12 12 h R w.boundA)) ∧
  (w.outputT.toBall rootDyadicConfig.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).weightedT.output.toBall rootDyadicConfig.prec))).inflate
      (quadratureErrorBound rationalQuadrature12 12 h R w.boundT))

instance (p : RootDerivativeParameters) (x h R : ℚ) (w : RootDerivativeCell) :
    Decidable (w.Valid p x h R) := by unfold Valid; infer_instance

theorem sound {t a : ℝ} (p : RootDerivativeParameters) (hp : p.Valid)
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ))
    (x h R : ℚ) (w : RootDerivativeCell) (hw : w.Valid p x h R) :
    (w.outputA.toBall rootDyadicConfig.prec).Contains
      (normalizedIntegral (thetaAa t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    (w.outputT.toBall rootDyadicConfig.prec).Contains
      (normalizedIntegral (thetaAtMidline t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    DiffContOnCl ℂ (thetaAa t a) (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) ∧
    DiffContOnCl ℂ (thetaAtMidline t a) (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) := by
  rcases hw with ⟨hh0,hhR,hcenter,hdisk,hdf,hnodes,houtA,houtT⟩
  have he := p.sound hp htl htu hal hau
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) he.height_lower
  have hbt := coarsen_contains (realInterval_contains htl htu) hp.1.2.1
  have hcenter' := coarsen_contains (horizontalCenterBall_contains hbt rootDyadicConfig x) hcenter
  let c : ℂ := (x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)
  have hbound : ∀ z ∈ closedBall c (R : ℝ),
      z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t ∧
      ‖thetaAa t a z‖ ≤ (w.boundA : ℝ) ∧ ‖thetaAtMidline t a z‖ ≤ (w.boundT : ℝ) := by
    intro z hz
    have hdz := coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk
    have hf := w.diskFunction.sound p he hdz hdf
    exact ⟨hf.2.2.1,hf.2.2.2,norm_le hf.1,norm_le hf.2.1⟩
  let S : Set ℂ := {z | z ∈ thetaRegular t ∧ z-(a : ℂ) ∈ thetaRegular t}
  have hA : DifferentiableOn ℂ (thetaAa t a) S := fun z hz =>
    (thetaAa_differentiableAt htpos a hz.1 hz.2).differentiableWithinAt
  have hT : DifferentiableOn ℂ (thetaAtMidline t a) S := fun z hz =>
    (thetaAtMidline_differentiableAt htpos a hz.1 hz.2).differentiableWithinAt
  have hanA := hA.diffContOnCl_ball (fun z hz => ⟨(hbound z hz).1,(hbound z hz).2.1⟩)
  have hanT := hT.diffContOnCl_ball (fun z hz => ⟨(hbound z hz).1,(hbound z hz).2.1⟩)
  have hnode (i : Fin 12) := (w.nodes i).sound p he w.center hcenter' h
    (rationalQuadrature12.node i) (rationalQuadrature12.weight i) (hnodes i)
  exact ⟨quadrature_enclosure rationalQuadrature12_exact rationalQuadrature12_nodes hh0 hhR
      hanA (fun z hz => (hbound z hz).2.2.1) (fun i => (hnode i).1) houtA,
    quadrature_enclosure rationalQuadrature12_exact rationalQuadrature12_nodes hh0 hhR
      hanT (fun z hz => (hbound z hz).2.2.2) (fun i => (hnode i).2) houtT,hanA,hanT⟩

end RootDerivativeCell
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.RootDerivativeCell.sound
