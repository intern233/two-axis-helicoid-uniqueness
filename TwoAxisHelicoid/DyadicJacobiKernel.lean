import TwoAxisHelicoid.DyadicJacobiParameters
import TwoAxisHelicoid.DyadicJacobiEuler

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiNormalization thetaA

structure DyadicJacobiKernelTrace where
  qx : DyadicExpressionTrace
  qinvx : DyadicExpressionTrace
  qrx : DyadicExpressionTrace
  qinvrx : DyadicExpressionTrace
  x : DyadicExpressionTrace
  rx : DyadicExpressionTrace
  pA : DyadicJacobiProductTrace
  pB : DyadicJacobiProductTrace
  pC : DyadicJacobiProductTrace
  pD : DyadicJacobiProductTrace
  eA : DyadicJacobiEulerTrace
  eB : DyadicJacobiEulerTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiKernelTrace

def output (w : DyadicJacobiKernelTrace) : DyadicBall := w.result.output

def inputs (p : DyadicJacobiParameters) (w : DyadicJacobiKernelTrace) : List DyadicBall :=
  [p.base.height,p.base.kappa.output,p.normalization.output,w.x.output,w.rx.output,
    w.pA.output,w.pB.output,w.pC.output,w.pD.output,w.eA.output,w.eB.output]

def Valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) : Prop :=
  let env := dyadicInputList [p.base.height,p.base.abscissa,z]
  w.qx.Valid cfg env jacobiQXExpression ∧ w.qinvx.Valid cfg env jacobiQInvXExpression ∧
  w.qrx.Valid cfg env jacobiQRXExpression ∧ w.qinvrx.Valid cfg env jacobiQInvRXExpression ∧
  w.x.Valid cfg env (jacobiPhysicalXExpression right) ∧
  w.rx.Valid cfg env jacobiPhysicalRXExpression ∧
  w.pA.Valid cfg.prec productError p.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.q.output w.qinvx.output ∧
  w.result.Valid cfg (dyadicInputList (w.inputs p)) (jacobiKernelResultExpression right)

instance (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) :
    Decidable (w.Valid cfg productError eulerError right p z) := by
  unfold Valid
  infer_instance

theorem sound (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    {t a : ℝ} {z : ℂ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (hzstrip : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (p : DyadicJacobiParameters)
    (hp : p.Valid cfg productError) (bz : DyadicBall)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (hbz : (bz.toBall cfg.prec).Contains z)
    (w : DyadicJacobiKernelTrace) (hw : w.Valid cfg productError eulerError right p bz) :
    (w.output.toBall cfg.prec).Contains (thetaA t a (z+I*((t/2 : ℝ) : ℂ))) := by
  rcases hw with ⟨hqx,hqix,hqrx,hqirx,hx,hrx,hpA,hpB,hpC,hpD,heA,heB,hresult⟩
  rcases p.sound cfg productError hbt hba hp with ⟨hq,hk,hc⟩
  have henv := dyadicInputList_contains (.cons hbt (.cons hba (.cons hbz .nil)))
  have hA := w.qx.sound cfg _ _ henv _ hqx
  have hB := w.qinvx.sound cfg _ _ henv _ hqix
  have hC := w.qrx.sound cfg _ _ henv _ hqrx
  have hD := w.qinvrx.sound cfg _ _ henv _ hqirx
  have hX := w.x.sound cfg _ _ henv _ hx
  have hRX := w.rx.sound cfg _ _ henv _ hrx
  rw [value_jacobiQXExpression] at hA
  rw [value_jacobiQInvXExpression] at hB
  rw [value_jacobiQRXExpression] at hC
  rw [value_jacobiQInvRXExpression] at hD
  rw [value_jacobiPhysicalXExpression] at hX
  rw [value_jacobiPhysicalRXExpression] at hRX
  have hPA := w.pA.sound cfg.prec productError hq hA hpA
  have hPB := w.pB.sound cfg.prec productError hq hB hpB
  have hPC := w.pC.sound cfg.prec productError hq hC hpC
  have hPD := w.pD.sound cfg.prec productError hq hD hpD
  have hEA := w.eA.sound cfg eulerError hq hA heA
  have hEB := w.eB.sound cfg eulerError hq hB heB
  have hpregion : ‖jacobiNome (1/t)‖*‖physicalJacobiX t z‖ < 1 := by
    rw [← norm_mul]
    exact (DyadicBall.norm_le_normUpper hA).trans_lt (by exact_mod_cast heA.2.2.1)
  have hmregion : ‖jacobiNome (1/t)‖*‖(physicalJacobiX t z)⁻¹‖ < 1 := by
    rw [← norm_mul]
    exact (DyadicBall.norm_le_normUpper hB).trans_lt (by exact_mod_cast heB.2.2.1)
  have hinputs := dyadicInputList_contains
    (.cons hbt (.cons hk (.cons hc (.cons hX (.cons hRX (.cons hPA (.cons hPB
      (.cons hPC (.cons hPD (.cons hEA (.cons hEB .nil)))))))))))
  have hout := w.result.sound cfg _ _ hinputs _ hresult
  rw [value_jacobiKernelResultExpression,
    ← dualProductIntegrand_eq_kernelResult ht hzstrip hpregion hmregion right,
    ← thetaA_eq_physical_product ht ha0 ha1 hzstrip hpregion hmregion] at hout
  exact hout

end DyadicJacobiKernelTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiKernelTrace.sound
