import TwoAxisHelicoid.TraceDataSpatialMeans
import TwoAxisHelicoid.SpatialMeanDisplacementData

namespace TwoAxisHelicoid.TraceData
set_option maxHeartbeats 1200000
attribute [local irreducible] slopingFluxParams

private theorem spatial_all_iff (n : Nat) (f : Fin n → Bool) :
    spatialAllNodes n f=true ↔ ∀ i, f i=true := by
  induction n with
  | zero => simp [spatialAllNodes]
  | succ n ih =>
    simp only [spatialAllNodes,Bool.and_eq_true,ih,Fin.forall_fin_succ]

private theorem spatial_sum_eq (n : Nat) (f : Fin n → Rat) :
    spatialRatSum n f=∑ i, f i := by
  induction n with
  | zero => simp [spatialRatSum]
  | succ n ih => rw [spatialRatSum,Fin.sum_univ_succ,ih]

private theorem spatial_rule_node (i : Fin 12) : spatialRuleNodes.get i=TwoAxisHelicoid.rationalQuadrature12.node i := by
  fin_cases i <;> rfl

private theorem spatial_rule_weight (i : Fin 12) : spatialRuleWeights.get i=TwoAxisHelicoid.rationalQuadrature12.weight i := by
  fin_cases i <;> rfl

private theorem spatial_coarsens {b a : ComplexBall} (h : b.coarsens a) : b.interpret.coarsens a.interpret := by
  change Rat.abs (a.center.re + -b.center.re)+Rat.abs (a.center.im + -b.center.im)+a.radius ≤ b.radius at h
  change |a.center.re + -b.center.re| + |a.center.im + -b.center.im| + a.radius ≤ b.radius
  simpa only [rat_abs_eq] using h

private theorem spatial_node_output (w : HorizontalRangeNode) (p : Nat) :
    (w.interpret.output.toBall p)=(w.output.toBall p).interpret := by
  change (w.weighted.interpret.output.toBall p)=_
  rw [DyadicExpressionTrace.interpret_output]
  rfl

private theorem spatial_sum_interpret (w : HorizontalRangeCell 12) :
    TwoAxisHelicoid.sumBalls (fun i => ((w.interpret.nodes i).output.toBall TwoAxisHelicoid.slopingFluxAnalyticSetup.config.prec))=
      (spatialMeanSum w).interpret := by
  change TwoAxisHelicoid.sumBalls (fun i => ((w.nodes i).interpret.output.toBall slopingFluxDataSetup.config.prec))=_
  simp only [spatial_node_output,TwoAxisHelicoid.sumBalls,spatialMeanSum,spatial_sum_eq,ComplexBall.interpret,QComplex.interpret]

private theorem spatial_disk_bound (w : HorizontalRangeCell 12) :
    w.interpret.diskBound TwoAxisHelicoid.slopingFluxAnalyticSetup=
    let b := w.diskFunction.output.toBall slopingFluxDataSetup.config.prec
    b.center.absUpper+b.radius := by
  change ((w.diskFunction.interpret.output.toBall slopingFluxDataSetup.config.prec).center.absUpper+
    (w.diskFunction.interpret.output.toBall slopingFluxDataSetup.config.prec).radius)=_
  rw [DyadicThetaATrace.interpret_output]
  let b := w.diskFunction.output.toBall slopingFluxDataSetup.config.prec
  change |b.center.re|+|b.center.im|+b.radius=Rat.abs b.center.re+Rat.abs b.center.im+b.radius
  rw [rat_abs_eq,rat_abs_eq]

theorem HorizontalRangeCell.spatial_mean_interpret {w : HorizontalRangeCell 12} {c : QComplex} {h R : Rat}
    (valid : w.spatialMeanValid c h R) :
    w.interpret.validAtRational TwoAxisHelicoid.slopingFluxAnalyticSetup TwoAxisHelicoid.rationalQuadrature12 12
      slopingFluxParams.interpret c.interpret h R := by
  rcases valid with ⟨len,rad,center,disk,wide,nodes,out⟩
  let prec := slopingFluxDataSetup.config.prec
  unfold TwoAxisHelicoid.HorizontalRangeCell.validAtRational
  refine ⟨len,rad,?_,?_,?_,?_,?_⟩
  · exact spatial_coarsens (b:=w.center.toBall prec) (a:=⟨c,0⟩) center
  · exact spatial_coarsens (b:=w.disk.toBall prec)
      (a:=spatialTraceInflate (w.center.toBall prec) R) disk
  · change w.diskFunction.interpret.HorizontalValid TwoAxisHelicoid.slopingFluxAnalyticSetup
      slopingFluxParams.q.interpret.output slopingFluxParams.abscissa.interpret
      slopingFluxParams.coefficient.interpret.output w.disk.interpret
    simpa only [DyadicExpressionTrace.interpret_output,DyadicCoefficientTrace.interpret_output] using
      DyadicThetaATrace.horizontal_valid_of_check_as TwoAxisHelicoid.slopingFluxAnalyticSetup slopingFluxDataSetup rfl
        slopingFluxParams.q.output slopingFluxParams.abscissa slopingFluxParams.coefficient.output w.disk w.diskFunction wide
  · intro i
    have hi := (spatial_all_iff _ _).mp nodes i
    rw [spatial_rule_node,spatial_rule_weight] at hi
    exact HorizontalRangeNode.valid_of_check_as TwoAxisHelicoid.slopingFluxAnalyticSetup slopingFluxDataSetup rfl
      slopingFluxParams w.center h _ _ (w.nodes i) hi
  · rw [spatial_sum_interpret,TwoAxisHelicoid.quadratureErrorBound,TwoAxisHelicoid.rationalQuadrature12_weightNorm,spatial_disk_bound]
    rw [show (1:Rat)+1=2 by norm_num]
    let diskBall := w.diskFunction.output.toBall prec
    let err := 2*((diskBall.center.absUpper+diskBall.radius)*(h/R)^12/(1-h/R))
    exact spatial_coarsens (b:=w.output.toBall prec) (a:=spatialTraceInflate (spatialMeanSum w) err) out

/-- A checked pure-arithmetic displacement always produces the same
analytic certificate, with the same endpoints and both rational bounds. -/
theorem CheckedSpatialMean.toAnalytic {f y l r a b} (c : CheckedSpatialMean f y l r a b) :
    TwoAxisHelicoid.CheckedHorizontalDisplacement f y l r a b := by
  induction c with
  | @cell l r R a b w ok =>
    obtain ⟨order,p,n,lo,hi⟩ := ok
    refine TwoAxisHelicoid.CheckedHorizontalDisplacement.cell (R:=R) ⟨w.positive.interpret,w.negative.interpret⟩ ?_
    unfold TwoAxisHelicoid.SpatialMeanDisplacementCell.Valid
    refine ⟨order,?_,?_,lo,hi⟩
    · exact HorizontalRangeCell.spatial_mean_interpret (w:=w.positive) (c:=⟨(l+r)/2,y⟩)
        (h:=(r-l)/2) (R:=R) p
    · exact HorizontalRangeCell.spatial_mean_interpret (w:=w.negative) (c:=⟨-((l+r)/2),-y⟩)
        (h:=(r-l)/2) (R:=R) n
  | join _ _ left right => exact .join left right

end TwoAxisHelicoid.TraceData
#print axioms TwoAxisHelicoid.TraceData.HorizontalRangeCell.spatial_mean_interpret
#print axioms TwoAxisHelicoid.TraceData.CheckedSpatialMean.toAnalytic
