import TwoAxisHelicoid.DyadicJacobiKernel
import TwoAxisHelicoid.JacobiFastExpressions
namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiNormalization thetaA
namespace DyadicJacobiKernelTrace
def FastValid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) : Prop :=
  let env := dyadicInputList [p.base.q.output,p.base.r.output,p.base.beta.output,w.x.output]
  w.qx.Valid cfg env (jacobiFastQXExpression right) ∧ w.qinvx.Valid cfg env (jacobiFastQInvXExpression right) ∧
  w.qrx.Valid cfg env (jacobiFastQRXExpression right) ∧ w.qinvrx.Valid cfg env (jacobiFastQInvRXExpression right) ∧
  w.x.Valid cfg (dyadicInputList [p.base.height,p.base.abscissa,z]) (jacobiPhysicalXExpression right) ∧
  w.rx.Valid cfg env (jacobiFastRXExpression right) ∧
  w.pA.Valid cfg.prec productError p.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.q.output w.qinvx.output ∧
  w.result.Valid cfg (dyadicInputList (w.inputs p)) (jacobiKernelResultExpression right)

instance (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (z : DyadicBall) (w : DyadicJacobiKernelTrace) :
    Decidable (w.FastValid cfg productError eulerError right p z) := by
  unfold FastValid
  infer_instance

theorem fast_sound (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    {t a : ℝ} {z : ℂ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (hzstrip : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (p : DyadicJacobiParameters)
    (hp : p.Valid cfg productError) (bz : DyadicBall)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (hbz : (bz.toBall cfg.prec).Contains z)
    (w : DyadicJacobiKernelTrace) (hw : w.FastValid cfg productError eulerError right p bz) :
    (w.output.toBall cfg.prec).Contains (thetaA t a (z+I*((t/2 : ℝ) : ℂ))) := by
  rcases hw with ⟨hqx,hqix,hqrx,hqirx,hx,hrx,hpA,hpB,hpC,hpD,heA,heB,hresult⟩
  rcases p.sound cfg productError hbt hba hp with ⟨hq,hk,hc⟩
  rcases p.base.sound cfg hbt hba hp.1 with ⟨_,hr,_,hbeta⟩
  have horig := dyadicInputList_contains (.cons hbt (.cons hba (.cons hbz .nil)))
  have hX := w.x.sound cfg _ _ horig _ hx
  rw [value_jacobiPhysicalXExpression] at hX
  have henv := dyadicInputList_contains (.cons hq (.cons hr (.cons hbeta (.cons hX .nil))))
  have hA := w.qx.sound cfg _ _ henv _ hqx
  have hB := w.qinvx.sound cfg _ _ henv _ hqix
  have hC := w.qrx.sound cfg _ _ henv _ hqrx
  have hD := w.qinvrx.sound cfg _ _ henv _ hqirx
  have hRX := w.rx.sound cfg _ _ henv _ hrx
  rcases value_jacobiFastSeeds right t a z with ⟨hvA,hvB,hvC,hvD,hvRX⟩
  rw [hvA] at hA
  rw [hvB] at hB
  rw [hvC] at hC
  rw [hvD] at hD
  rw [hvRX] at hRX
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
#print axioms TwoAxisHelicoid.DyadicJacobiKernelTrace.fast_sound
