import TwoAxisHelicoid.HorizontalRangeParameters
import TwoAxisHelicoid.QuadratureEnclosure

namespace TwoAxisHelicoid
open ComplexBall Metric
attribute [local irreducible] thetaA thetaJet

structure HorizontalRangeNode where
  point : DyadicBall
  function : DyadicThetaATrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace HorizontalRangeNode

def output (w : HorizontalRangeNode) : DyadicBall := w.weighted.output

def Valid (s : HorizontalRangeSetup) (p : RangeDyadicParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : HorizontalRangeNode) : Prop :=
  (w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node))) ∧
  w.function.HorizontalValid s p.q.output p.abscissa p.coefficient.output w.point ∧
  w.weighted.Valid s.config (threeDyadic w.function.output .zero .zero)
    (.mul (.rational weight) (.input 0))

instance (s : HorizontalRangeSetup) (p : RangeDyadicParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : HorizontalRangeNode) : Decidable (w.Valid s p center h node weight) := by
  unfold Valid
  infer_instance

def check (s : HorizontalRangeSetup) (p : RangeDyadicParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : HorizontalRangeNode) : Bool :=
  decide ((w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node)))) &&
  w.function.horizontalCheck s p.q.output p.abscissa p.coefficient.output w.point &&
  w.weighted.check s.config (threeDyadic w.function.output .zero .zero)
    (.mul (.rational weight) (.input 0))

theorem check_eq_true (s : HorizontalRangeSetup) (p : RangeDyadicParameters) (center : DyadicBall)
    (h node weight : ℚ) (w : HorizontalRangeNode) :
    w.check s p center h node weight = true ↔ w.Valid s p center h node weight := by
  simp only [check, Valid, Bool.and_eq_true, decide_eq_true_eq,
    DyadicThetaATrace.horizontalCheck_eq_true, DyadicExpressionTrace.check_eq_true, and_assoc]

theorem sound (s : HorizontalRangeSetup) (hs : s.Valid) {t a : ℝ} {c : ℂ}
    (p : RangeDyadicParameters) (center : DyadicBall) (ht : (s.lower : ℝ) ≤ t)
    (hq : (p.q.output.toBall s.config.prec).Contains (Complex.exp (-Real.pi*t)))
    (ha : (p.abscissa.toBall s.config.prec).Contains (a : ℂ))
    (hc : (p.coefficient.output.toBall s.config.prec).Contains (thetaACoefficient t a))
    (hcenter : (center.toBall s.config.prec).Contains c)
    (h node weight : ℚ) (w : HorizontalRangeNode) (hw : w.Valid s p center h node weight) :
    (w.output.toBall s.config.prec).Contains
      ((weight : ℂ)*thetaA t a (c+(h : ℂ)*(node : ℂ))) := by
  have hz := coarsen_contains (add_contains hcenter (rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hf := (w.function.horizontal_sound s hs ht hq ha hc hz hw.2.1).1
  have hzero := DyadicBall.zero_contains s.config.prec
  have hout := w.weighted.sound s.config _ _ (threeDyadic_contains hf hzero hzero) _ hw.2.2
  simpa only [output, BallExpression.value, BallExpression.value_rational, threeValues] using hout

end HorizontalRangeNode

/-- A cell can use any already proved rational quadrature rule. -/
structure HorizontalRangeCell (K : ℕ) where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicThetaATrace
  nodes : Fin K → HorizontalRangeNode
  output : DyadicBall

namespace HorizontalRangeCell

def diskBound {K : ℕ} (s : HorizontalRangeSetup) (w : HorizontalRangeCell K) : ℚ :=
  (w.diskFunction.output.toBall s.config.prec).center.absUpper+
    (w.diskFunction.output.toBall s.config.prec).radius

def Valid {K : ℕ} (s : HorizontalRangeSetup) (q : QuadratureRule K) (order : ℕ)
    (p : RangeDyadicParameters) (x h R : ℚ) (w : HorizontalRangeCell K) : Prop :=
  0 ≤ h ∧ h < R ∧
  (w.center.toBall s.config.prec).coarsens
    (horizontalCenterBall s.config (p.height.toBall s.config.prec) x) ∧
  (w.disk.toBall s.config.prec).coarsens ((w.center.toBall s.config.prec).inflate R) ∧
  w.diskFunction.HorizontalValid s p.q.output p.abscissa p.coefficient.output w.disk ∧
  (∀ i : Fin K, (w.nodes i).Valid s p w.center h (q.node i) (q.weight i)) ∧
  (w.output.toBall s.config.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).output.toBall s.config.prec))).inflate
      (quadratureErrorBound q order h R (w.diskBound s)))

instance {K : ℕ} (s : HorizontalRangeSetup) (q : QuadratureRule K) (order : ℕ)
    (p : RangeDyadicParameters) (x h R : ℚ) (w : HorizontalRangeCell K) :
    Decidable (w.Valid s q order p x h R) := by unfold Valid; infer_instance

theorem sound {K : ℕ} (s : HorizontalRangeSetup) (hs : s.Valid)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo thi alo ahi : ℚ} {t a : ℝ} (p : RangeDyadicParameters)
    (hp : p.HorizontalValid s tlo thi alo ahi)
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ))
    (x h R : ℚ) (w : HorizontalRangeCell K) (hw : w.Valid s q order p x h R) :
    (w.output.toBall s.config.prec).Contains
      (normalizedIntegral (thetaA t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) ∧
    DiffContOnCl ℂ (thetaA t a)
      (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) := by
  rcases hw with ⟨hh0, hhR, hcenter, hdisk, hdf, hnodes, hout⟩
  rcases p.horizontal_sound s hs hp htl htu hal hau with ⟨ht, hq, ha, hc⟩
  have htpos : 0 < t := (s.lower_pos hs).trans_le ht
  have hbt := coarsen_contains (realInterval_contains htl htu) hp.2.1
  have hcenter' := coarsen_contains (horizontalCenterBall_contains hbt s.config x) hcenter
  let c : ℂ := (x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)
  have hbound : ∀ z ∈ closedBall c (R : ℝ),
      z ∈ thetaRegular t ∧ ‖thetaA t a z‖ ≤ ((w.diskBound s) : ℝ) := by
    intro z hz
    have hdz := coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk
    have hf := w.diskFunction.horizontal_sound s hs ht hq ha hc hdz hdf
    exact ⟨hf.2, norm_le hf.1⟩
  have han : DiffContOnCl ℂ (thetaA t a) (ball c (R : ℝ)) :=
    (thetaA_differentiableOn htpos a).diffContOnCl_ball (fun z hz => (hbound z hz).1)
  exact ⟨quadrature_enclosure hqexact hqnodes hh0 hhR han (fun z hz => (hbound z hz).2)
    (fun i => (w.nodes i).sound s hs p w.center ht hq ha hc hcenter'
      h (q.node i) (q.weight i) (hnodes i)) hout, han⟩

end HorizontalRangeCell
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HorizontalRangeCell.sound
