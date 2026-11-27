import TwoAxisHelicoid.JacobiChordExpressions
import TwoAxisHelicoid.DyadicJacobiParameters
import TwoAxisHelicoid.DyadicJacobiEuler
import TwoAxisHelicoid.DyadicBooleanCheck

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000
attribute [local irreducible] jacobiPairProduct jacobiFactorProduct jacobiNormalization

@[local simp] private theorem chord_trace_const_i : (⟨(0 : ℝ),1⟩ : ℂ) = I := rfl

-- BEGIN FINITE DEFINITIONS
def jacobiChordMinusIExpression : BallExpression := .sub (.input 0) (.const ⟨0,1⟩)
def jacobiChordPlusIExpression : BallExpression := .add (.input 0) (.const ⟨0,1⟩)

structure DyadicJacobiChordParameters where
  base : DyadicJacobiParameters
  nomeHalf : DyadicExpressionTrace
  chordH : DyadicExpressionTrace
  chordK : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiChordParameters

def Valid (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiChordParameters) : Prop :=
  p.base.Valid cfg err ∧
  p.nomeHalf.check cfg (dyadicInputList [p.base.base.height]) jacobiChordNomeExpression = true ∧
  p.chordH.check cfg (dyadicInputList [p.nomeHalf.output]) jacobiChordHExpression = true ∧
  p.chordK.check cfg (dyadicInputList [p.nomeHalf.output]) jacobiChordKExpression = true

instance (cfg : BallConfig) (err : ℕ) (p : DyadicJacobiChordParameters) : Decidable (p.Valid cfg err) := by
  unfold Valid
  infer_instance

end DyadicJacobiChordParameters

structure DyadicJacobiChordTrace where
  u : DyadicExpressionTrace
  uMinusI : DyadicExpressionTrace
  uPlusI : DyadicExpressionTrace
  x : DyadicExpressionTrace
  invx : DyadicExpressionTrace
  qx : DyadicExpressionTrace
  qinvx : DyadicExpressionTrace
  qrx : DyadicExpressionTrace
  qinvrx : DyadicExpressionTrace
  rx : DyadicExpressionTrace
  pA : DyadicJacobiProductTrace
  pB : DyadicJacobiProductTrace
  pC : DyadicJacobiProductTrace
  pD : DyadicJacobiProductTrace
  eA : DyadicJacobiEulerTrace
  eB : DyadicJacobiEulerTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicJacobiChordTrace

def output (w : DyadicJacobiChordTrace) : DyadicBall := w.result.output

def seedInputs (p : DyadicJacobiChordParameters) (w : DyadicJacobiChordTrace) : List DyadicBall :=
  [p.base.base.q.output,p.base.base.r.output,p.base.base.beta.output,w.x.output,w.invx.output]

def inputs (p : DyadicJacobiChordParameters) (w : DyadicJacobiChordTrace) : List DyadicBall :=
  [p.base.base.height,p.base.base.kappa.output,p.base.normalization.output,w.u.output,w.x.output,w.rx.output,
    w.pA.output,w.pB.output,w.pC.output,w.pD.output,w.eA.output,w.eB.output,p.chordK.output]

def Valid (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (z : DyadicBall) (w : DyadicJacobiChordTrace) : Prop :=
  let uenv := dyadicInputList [w.u.output]
  let env := dyadicInputList (w.seedInputs p)
  w.u.check cfg (dyadicInputList [p.chordH.output,p.chordK.output,z]) jacobiChordUExpression = true ∧
  w.uMinusI.check cfg uenv jacobiChordMinusIExpression = true ∧ 0 < w.uMinusI.output.lower ∧
  w.uPlusI.check cfg uenv jacobiChordPlusIExpression = true ∧ 0 < w.uPlusI.output.lower ∧
  w.x.check cfg uenv jacobiChordXExpression = true ∧
  w.invx.check cfg uenv jacobiChordInvXExpression = true ∧
  w.qx.check cfg env jacobiChordQXExpression = true ∧
  w.qinvx.check cfg env jacobiChordQInvXExpression = true ∧
  w.qrx.check cfg env jacobiChordQRXExpression = true ∧
  w.qinvrx.check cfg env jacobiChordQInvRXExpression = true ∧
  w.rx.check cfg env jacobiChordRXExpression = true ∧
  w.pA.Valid cfg.prec productError p.base.base.q.output w.qx.output ∧
  w.pB.Valid cfg.prec productError p.base.base.q.output w.qinvx.output ∧
  w.pC.Valid cfg.prec productError p.base.base.q.output w.qrx.output ∧
  w.pD.Valid cfg.prec productError p.base.base.q.output w.qinvrx.output ∧
  w.eA.Valid cfg eulerError p.base.base.q.output w.qx.output ∧
  w.eB.Valid cfg eulerError p.base.base.q.output w.qinvx.output ∧
  w.result.check cfg (dyadicInputList (w.inputs p)) jacobiChordResultExpression = true

instance (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (z : DyadicBall) (w : DyadicJacobiChordTrace) :
    Decidable (w.Valid cfg productError eulerError p z) := by
  unfold Valid
  infer_instance

end DyadicJacobiChordTrace
-- END FINITE DEFINITIONS

theorem DyadicExpressionTrace.chord_checked_sound (cfg : BallConfig) (env : ℕ → DyadicBall)
    (values : ℕ → ℂ) (h : ∀ i, ((env i).toBall cfg.prec).Contains (values i))
    (e : BallExpression) (w : DyadicExpressionTrace) (hw : w.check cfg env e = true) :
    (w.output.toBall cfg.prec).Contains (e.value values) :=
  w.sound cfg env values h e ((DyadicExpressionTrace.check_eq_true _ _ _ _).mp hw)

theorem DyadicJacobiChordParameters.sound_geometry (cfg : BallConfig) (err : ℕ)
    {t : ℝ} (p : DyadicJacobiChordParameters)
    (ht : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ)) (hp : p.Valid cfg err) :
    (p.chordH.output.toBall cfg.prec).Contains (leftChordH (leftNome t) : ℂ) ∧
    (p.chordK.output.toBall cfg.prec).Contains (leftChordK (leftNome t) : ℂ) := by
  have he := dyadicInputList_contains (.cons ht .nil)
  have hn := p.nomeHalf.chord_checked_sound cfg _ _ he _ hp.2.1
  rw [value_jacobiChordNomeExpression] at hn
  have hen := dyadicInputList_contains (.cons hn .nil)
  have hh := p.chordH.chord_checked_sound cfg _ _ hen _ hp.2.2.1
  have hk := p.chordK.chord_checked_sound cfg _ _ hen _ hp.2.2.2
  rw [value_jacobiChordHExpression] at hh
  rw [value_jacobiChordKExpression] at hk
  exact ⟨hh,hk⟩

theorem dyadic_ne_zero_of_lower_pos {prec : ℕ} {b : DyadicBall} {z : ℂ}
    (hb : (b.toBall prec).Contains z) (hpos : 0 < b.lower) : z ≠ 0 := by
  apply ComplexBall.ne_zero_of_lower_pos hb
  rw [DyadicBall.lower_toBall]
  exact div_pos (Int.cast_pos.mpr hpos) (by exact_mod_cast DyadicBall.denominator_pos prec)

theorem DyadicJacobiChordTrace.sound (cfg : BallConfig) (productError eulerError : ℕ)
    {t a : ℝ} {z : ℂ} (ht : 0 < t) (p : DyadicJacobiChordParameters)
    (hp : p.Valid cfg productError) (bz : DyadicBall)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (hbz : (bz.toBall cfg.prec).Contains z)
    (w : DyadicJacobiChordTrace) (hw : w.Valid cfg productError eulerError p bz) :
    (w.output.toBall cfg.prec).Contains (jacobiChordKernel t a z) ∧
      DifferentiableAt ℂ (jacobiChordKernel t a) z := by
  rcases hw with ⟨hu,hum,hum0,hup,hup0,hx,hix,hqx,hqix,hqrx,hqirx,hrx,
    hpA,hpB,hpC,hpD,heA,heB,hresult⟩
  rcases p.base.sound cfg productError hbt hba hp.1 with ⟨hq,hk,hc⟩
  have hbbase := p.base.base.sound cfg hbt hba hp.1.1
  rcases p.sound_geometry cfg productError hbt hp with ⟨hH,hK⟩
  have huenv := dyadicInputList_contains (.cons hH (.cons hK (.cons hbz .nil)))
  have hU := w.u.chord_checked_sound cfg _ _ huenv _ hu
  rw [value_jacobiChordUExpression] at hU
  have hxenv := dyadicInputList_contains (.cons hU .nil)
  have hUM := w.uMinusI.chord_checked_sound cfg _ _ hxenv _ hum
  have hUP := w.uPlusI.chord_checked_sound cfg _ _ hxenv _ hup
  simp [jacobiChordMinusIExpression, BallExpression.value, complexInputList, QComplex.val] at hUM
  simp [jacobiChordPlusIExpression, BallExpression.value, complexInputList, QComplex.val] at hUP
  have hdenM : jacobiChordPoint t z-I ≠ 0 := dyadic_ne_zero_of_lower_pos hUM hum0
  have hdenP : jacobiChordPoint t z+I ≠ 0 := dyadic_ne_zero_of_lower_pos hUP hup0
  have hX := w.x.chord_checked_sound cfg _ _ hxenv _ hx
  have hIX := w.invx.chord_checked_sound cfg _ _ hxenv _ hix
  rw [value_jacobiChordXExpression] at hX
  rw [value_jacobiChordInvXExpression] at hIX
  have henv := dyadicInputList_contains
    (.cons hq (.cons hbbase.2.1 (.cons hbbase.2.2.2 (.cons hX (.cons hIX .nil)))))
  have hA := w.qx.chord_checked_sound cfg _ _ henv _ hqx
  have hB := w.qinvx.chord_checked_sound cfg _ _ henv _ hqix
  have hC := w.qrx.chord_checked_sound cfg _ _ henv _ hqrx
  have hD := w.qinvrx.chord_checked_sound cfg _ _ henv _ hqirx
  have hRX := w.rx.chord_checked_sound cfg _ _ henv _ hrx
  have hseed := value_jacobiChordSeeds t a (jacobiChordX (jacobiChordPoint t z))
  rw [hseed.1] at hA
  rw [hseed.2.1] at hB
  rw [hseed.2.2.1] at hC
  rw [hseed.2.2.2.1] at hD
  rw [hseed.2.2.2.2] at hRX
  have hPA := w.pA.sound cfg.prec productError hq hA hpA
  have hPB := w.pB.sound cfg.prec productError hq hB hpB
  have hPC := w.pC.sound cfg.prec productError hq hC hpC
  have hPD := w.pD.sound cfg.prec productError hq hD hpD
  have hEA := w.eA.sound cfg eulerError hq hA heA
  have hEB := w.eB.sound cfg eulerError hq hB heB
  have hpregion : ‖jacobiNome (1/t)‖*‖jacobiChordX (jacobiChordPoint t z)‖ < 1 := by
    rw [← norm_mul]
    exact (DyadicBall.norm_le_normUpper hA).trans_lt (by exact_mod_cast heA.2.2.1)
  have hmregion : ‖jacobiNome (1/t)‖*‖(jacobiChordX (jacobiChordPoint t z))⁻¹‖ < 1 := by
    rw [← norm_mul]
    exact (DyadicBall.norm_le_normUpper hB).trans_lt (by exact_mod_cast heB.2.2.1)
  have hx0 : jacobiChordX (jacobiChordPoint t z) ≠ 0 := div_ne_zero hdenP hdenM
  have hinputs := dyadicInputList_contains
    (.cons hbt (.cons hk (.cons hc (.cons hU (.cons hX (.cons hRX (.cons hPA (.cons hPB
      (.cons hPC (.cons hPD (.cons hEA (.cons hEB (.cons hK .nil)))))))))))))
  have hout := w.result.chord_checked_sound cfg _ _ hinputs _ hresult
  rw [value_jacobiChordResultExpression, ← jacobiChordKernel_eq_result ht hx0 hpregion hmregion] at hout
  exact ⟨hout, jacobiChordKernel_differentiableAt ht hdenM hdenP hpregion hmregion⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiChordTrace.sound
