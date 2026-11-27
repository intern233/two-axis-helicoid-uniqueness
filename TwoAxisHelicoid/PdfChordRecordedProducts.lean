import TwoAxisHelicoid.PdfChordLiteral

namespace TwoAxisHelicoid.PdfVertical

/-- Intermediate products prevent a kernel reduction of the full Jacobi
expression from retaining the evaluation of every previous factor. -/
inductive ProductSteps where
  | start
  | step (previous : ProductSteps) (value power : CGrid)

def ProductSteps.size : ProductSteps → Nat
  | .start => 0
  | .step previous _ _ => previous.size+1

def ProductSteps.last (log : Bool) (seed : CGrid) : ProductSteps → CGrid × CGrid
  | .start => (if log then .ofInt 0 else .ofInt 1,seed)
  | .step _ value power => (value,power)

def productStep (log : Bool) (q : Grid) (state : CGrid × CGrid) : CGrid × CGrid :=
  let factor := (CGrid.ofInt 1).sub state.2
  (if log then state.1.add (state.2.neg.div factor) else state.1.mul factor,state.2.scale q)

def ProductSteps.check (log : Bool) (q : Grid) (seed : CGrid) : ProductSteps → Bool
  | .start => true
  | .step previous value power =>
    previous.check log q seed && decide (productStep log q (previous.last log seed)=(value,power))

theorem ProductSteps.correct (log : Bool) (q : Grid) (seed : CGrid) (w : ProductSteps)
    (valid : w.check log q seed=true) : chordFinite log q seed w.size=w.last log seed := by
  induction w with
  | start => rfl
  | step prev value power ih =>
    obtain ⟨rest,step⟩ := Bool.and_eq_true_iff.mp valid
    change productStep log q (chordFinite log q seed prev.size)=(value,power)
    rw [ih rest]
    exact of_decide_eq_true step

def productWithRemainder (log : Bool) (q : Grid) (seed : CGrid) (state : CGrid × CGrid) : CGrid :=
  let (v,p) := state
  let one := Grid.ofInt 1
  let s := Grid.point q.mag
  let tau := Grid.point p.mag
  let den := one.sub s
  let err := if log then tau.divPos (den.mul (one.sub tau)) else
    (((Grid.ofInt 2).mul (Grid.point v.mag)).mul tau).divPos den
  let flag := q.ok && seed.ok && p.ok && v.ok && err.ok &&
    decide (q.mag<Grid.denom ∧ p.mag+q.mag≤Grid.denom ∧ p.mag<Grid.denom) &&
    (!log || decide (seed.mag<Grid.denom))
  (v.widen err.hi).guard flag

structure RecordedProduct where
  steps : ProductSteps
  result : CGrid

def RecordedProduct.valid (w : RecordedProduct) (log : Bool) (q : Grid) (seed : CGrid) : Bool :=
  decide (w.steps.size=10) && w.steps.check log q seed &&
    decide (productWithRemainder log q seed (w.steps.last log seed)=w.result)

theorem RecordedProduct.correct (w : RecordedProduct) {log : Bool} {q : Grid} {seed : CGrid}
    (valid : w.valid log q seed=true) : chordEulerProduct log q seed=w.result := by
  simp only [RecordedProduct.valid,Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨⟨size,steps⟩,tail⟩ := valid
  change productWithRemainder log q seed (chordFinite log q seed 10)=_
  have eq := w.steps.correct log q seed steps
  rw [size] at eq
  rw [eq,tail]

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.RecordedProduct.correct
