import TwoAxisHelicoid.HorizontalRangeCell

namespace TwoAxisHelicoid

/-- A quadrature cell centered at any specified rational point of the
complex plane. The surrounding disk certifies both holomorphicity
and the norm bound for Taylor's remainder. -/
def HorizontalRangeCell.validAtRational {K : ℕ} (s : HorizontalRangeSetup)
    (rule : QuadratureRule K) (order : ℕ) (p : RangeDyadicParameters)
    (c : QComplex) (h R : ℚ) (w : HorizontalRangeCell K) : Prop :=
  0≤h ∧ h<R ∧ (w.center.toBall s.config.prec).coarsens ⟨c,0⟩ ∧
  (w.disk.toBall s.config.prec).coarsens ((w.center.toBall s.config.prec).inflate R) ∧
  w.diskFunction.HorizontalValid s p.q.output p.abscissa p.coefficient.output w.disk ∧
  (∀ i, (w.nodes i).Valid s p w.center h (rule.node i) (rule.weight i)) ∧
  (w.output.toBall s.config.prec).coarsens
    ((sumBalls (fun i => (w.nodes i).output.toBall s.config.prec)).inflate
      (quadratureErrorBound rule order h R (w.diskBound s)))

instance {K : ℕ} (s : HorizontalRangeSetup) (rule : QuadratureRule K) (order : ℕ)
    (p : RangeDyadicParameters) (c : QComplex) (h R : ℚ) (w : HorizontalRangeCell K) :
    Decidable (w.validAtRational s rule order p c h R) := by
  unfold HorizontalRangeCell.validAtRational
  infer_instance

end TwoAxisHelicoid
