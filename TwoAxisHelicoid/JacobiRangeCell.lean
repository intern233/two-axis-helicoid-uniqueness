import TwoAxisHelicoid.DyadicJacobiKernel
import TwoAxisHelicoid.JacobiDiskGeometry
import TwoAxisHelicoid.QuadratureEnclosure

namespace TwoAxisHelicoid
open Complex ComplexBall Metric
set_option maxHeartbeats 800000
attribute [local irreducible] thetaA

structure JacobiRangeNode where
  point : DyadicBall
  function : DyadicJacobiKernelTrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace JacobiRangeNode

def output (w : JacobiRangeNode) : DyadicBall := w.weighted.output

def Valid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) : Prop :=
  (w.point.toBall cfg.prec).coarsens
    (ComplexBall.add (center.toBall cfg.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid cfg productError eulerError right p w.point ∧
  w.weighted.Valid cfg (dyadicInputList [w.function.output])
    (.mul (.rational weight) (.input 0))

instance (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) : Decidable (w.Valid cfg productError eulerError right p center h node weight) := by
  unfold Valid
  infer_instance

theorem sound (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (center : DyadicBall) (x h node weight : ℚ)
    (hcenter : (center.toBall cfg.prec).Contains (x : ℂ))
    (w : JacobiRangeNode) (hw : w.Valid cfg productError eulerError right p center h node weight) :
    (w.output.toBall cfg.prec).Contains ((weight : ℂ)*
      thetaA t a (((x : ℂ)+(h : ℂ)*(node : ℂ))+I*((t/2 : ℝ) : ℂ))) := by
  have hz := coarsen_contains (add_contains hcenter (rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hlat : ((x : ℂ)+(h : ℂ)*(node : ℂ))+I*((t/2 : ℝ) : ℂ) ∉
      (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast] using
      rhombic_midline_not_mem ht ((x : ℝ)+(h : ℝ)*(node : ℝ))
  have hf := w.function.sound cfg productError eulerError right ht ha0 ha1 hlat p hp
    w.point hbt hba hz hw.2.1
  have he := dyadicInputList_contains (.cons hf .nil)
  have hout := w.weighted.sound cfg _ _ he _ hw.2.2
  simpa only [output, BallExpression.value, BallExpression.value_rational,
    complexInputList, List.getElem?_cons_zero, Option.getD_some] using hout

end JacobiRangeNode

structure JacobiRangeCell (K : ℕ) where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicJacobiKernelTrace
  nodes : Fin K → JacobiRangeNode
  output : DyadicBall

namespace JacobiRangeCell

def diskBound {K : ℕ} (cfg : BallConfig) (w : JacobiRangeCell K) : ℚ :=
  w.diskFunction.output.normUpper cfg.prec

def Valid {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiParameters)
    (tlo x h R : ℚ) (w : JacobiRangeCell K) : Prop :=
  0 ≤ h ∧ h < R ∧ JacobiDiskGuard tlo x R ∧
  (w.center.toBall cfg.prec).coarsens (ComplexBall.rational x) ∧
  (w.disk.toBall cfg.prec).coarsens ((w.center.toBall cfg.prec).inflate R) ∧
  w.diskFunction.Valid cfg productError eulerError right p w.disk ∧
  (∀ i : Fin K, (w.nodes i).Valid cfg productError eulerError right p w.center h (q.node i) (q.weight i)) ∧
  (w.output.toBall cfg.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).output.toBall cfg.prec))).inflate
      (quadratureErrorBound q order h R (w.diskBound cfg)))

instance {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiParameters)
    (tlo x h R : ℚ) (w : JacobiRangeCell K) :
    Decidable (w.Valid cfg productError eulerError right q order p tlo x h R) := by
  unfold Valid
  infer_instance

theorem sound {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo x h R : ℚ} {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (htl : (tlo : ℝ) ≤ t) (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : JacobiRangeCell K) (hw : w.Valid cfg productError eulerError right q order p tlo x h R) :
    (w.output.toBall cfg.prec).Contains
      (normalizedIntegral (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ))) (x : ℂ) (h : ℝ)) ∧
    DiffContOnCl ℂ (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ)))
      (ball (x : ℂ) (R : ℝ)) := by
  rcases hw with ⟨hh0,hhR,hg,hcenter,hdisk,hdf,hnodes,hout⟩
  have hcenter' := coarsen_contains (rational_contains x) hcenter
  have hbound : ∀ z ∈ closedBall (x : ℂ) (R : ℝ),
      ‖thetaA t a (z+I*((t/2 : ℝ) : ℂ))‖ ≤ (w.diskBound cfg : ℝ) := by
    intro z hz
    have hdz := coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk
    exact DyadicBall.norm_le_normUpper
      (w.diskFunction.sound cfg productError eulerError right ht ha0 ha1
        (jacobiDiskGuard_not_mem ht htl hg hz) p hp w.disk hbt hba hdz hdf)
  have han := centeredThetaA_disk_analytic ht htl hg a
  exact ⟨quadrature_enclosure hqexact hqnodes hh0 hhR han hbound
    (fun i => (w.nodes i).sound cfg productError eulerError right ht ha0 ha1 p hp hbt hba
      w.center x h (q.node i) (q.weight i) hcenter' (hnodes i)) hout, han⟩

end JacobiRangeCell
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.JacobiRangeCell.sound
