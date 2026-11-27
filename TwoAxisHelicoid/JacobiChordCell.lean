import TwoAxisHelicoid.DyadicJacobiChord
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric MeasureTheory
set_option maxHeartbeats 1000000

-- BEGIN FINITE DEFINITIONS
structure JacobiChordRangeNode where
  point : DyadicBall
  function : DyadicJacobiChordTrace
  weighted : DyadicExpressionTrace
  deriving Repr

namespace JacobiChordRangeNode

def output (w : JacobiChordRangeNode) : DyadicBall := w.weighted.output

def Valid (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiChordRangeNode) : Prop :=
  (w.point.toBall cfg.prec).coarsens
    (ComplexBall.add (center.toBall cfg.prec) (ComplexBall.rational (h*node))) ∧
  w.function.Valid cfg productError eulerError p w.point ∧
  w.weighted.check cfg (dyadicInputList [w.function.output])
    (.mul (.rational weight) (.input 0)) = true

instance (cfg : BallConfig) (productError eulerError : ℕ)
    (p : DyadicJacobiChordParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiChordRangeNode) : Decidable (w.Valid cfg productError eulerError p center h node weight) := by
  unfold Valid
  infer_instance

end JacobiChordRangeNode

structure JacobiChordRangeCell (K : ℕ) where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : DyadicJacobiChordTrace
  nodes : Fin K → JacobiChordRangeNode
  output : DyadicBall

namespace JacobiChordRangeCell

def diskBound {K : ℕ} (cfg : BallConfig) (w : JacobiChordRangeCell K) : ℚ :=
  w.diskFunction.output.normUpper cfg.prec

def Valid {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiChordParameters)
    (x h R : ℚ) (w : JacobiChordRangeCell K) : Prop :=
  0 ≤ h ∧ h < R ∧
  (w.center.toBall cfg.prec).coarsens (ComplexBall.rational x) ∧
  (w.disk.toBall cfg.prec).coarsens ((w.center.toBall cfg.prec).inflate R) ∧
  w.diskFunction.Valid cfg productError eulerError p w.disk ∧
  (∀ i : Fin K, (w.nodes i).Valid cfg productError eulerError p w.center h (q.node i) (q.weight i)) ∧
  (w.output.toBall cfg.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).output.toBall cfg.prec))).inflate
      (quadratureErrorBound q order h R (w.diskBound cfg)))

instance {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiChordParameters)
    (x h R : ℚ) (w : JacobiChordRangeCell K) :
    Decidable (w.Valid cfg productError eulerError q order p x h R) := by
  unfold Valid
  infer_instance

end JacobiChordRangeCell
-- END FINITE DEFINITIONS

theorem JacobiChordRangeNode.sound (cfg : BallConfig) (productError eulerError : ℕ)
    {t a : ℝ} (ht : 0 < t) (p : DyadicJacobiChordParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (center : DyadicBall) (x h node weight : ℚ)
    (hcenter : (center.toBall cfg.prec).Contains (x : ℂ))
    (w : JacobiChordRangeNode) (hw : w.Valid cfg productError eulerError p center h node weight) :
    (w.output.toBall cfg.prec).Contains ((weight : ℂ)*
      jacobiChordKernel t a ((x : ℂ)+(h : ℂ)*(node : ℂ))) := by
  have hz := coarsen_contains (add_contains hcenter (rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hf := (w.function.sound cfg productError eulerError ht p hp w.point hbt hba hz hw.2.1).1
  have he := dyadicInputList_contains (.cons hf .nil)
  have hout := w.weighted.chord_checked_sound cfg _ _ he _ hw.2.2
  simpa only [JacobiChordRangeNode.output, BallExpression.value, BallExpression.value_rational,
    complexInputList, List.getElem?_cons_zero, Option.getD_some] using hout

theorem JacobiChordRangeCell.sound {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {x h R : ℚ} {t a : ℝ} (ht : 0 < t)
    (p : DyadicJacobiChordParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : JacobiChordRangeCell K) (hw : w.Valid cfg productError eulerError q order p x h R) :
    (w.output.toBall cfg.prec).Contains (normalizedIntegral (jacobiChordKernel t a) (x : ℂ) (h : ℝ)) ∧
    DiffContOnCl ℂ (jacobiChordKernel t a) (ball (x : ℂ) (R : ℝ)) := by
  rcases hw with ⟨hh0,hhR,hcenter,hdisk,hdf,hnodes,hout⟩
  have hcenter' := coarsen_contains (rational_contains x) hcenter
  have hpoint (z : ℂ) (hz : z ∈ closedBall (x : ℂ) (R : ℝ)) :=
    w.diskFunction.sound cfg productError eulerError ht p hp w.disk hbt hba
      (coarsen_contains (inflate_contains hcenter' (mem_closedBall_iff_norm.mp hz)) hdisk) hdf
  have hbound : ∀ z ∈ closedBall (x : ℂ) (R : ℝ),
      ‖jacobiChordKernel t a z‖ ≤ (w.diskBound cfg : ℝ) := by
    intro z hz
    exact DyadicBall.norm_le_normUpper (hpoint z hz).1
  have hd : DifferentiableOn ℂ (jacobiChordKernel t a) (closedBall (x : ℂ) (R : ℝ)) := by
    intro z hz
    exact (hpoint z hz).2.differentiableWithinAt
  have han := hd.diffContOnCl_ball (fun _ hz => hz)
  exact ⟨quadrature_enclosure hqexact hqnodes hh0 hhR han hbound
    (fun i => (w.nodes i).sound cfg productError eulerError ht p hp hbt hba
      w.center x h (q.node i) (q.weight i) hcenter' (hnodes i)) hout, han⟩

def combineJacobiChordCells {K N : ℕ} (cfg : BallConfig) (boundary : ℕ → ℚ)
    (cells : Fin N → JacobiChordRangeCell K) : ComplexBall :=
  sumBalls (fun i => scale (boundary (i+1)-boundary i) ((cells i).output.toBall cfg.prec))

theorem jacobiChord_composite_contains_of_nome {K N : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0 < t) (hq : leftNome t ≤ 1/3)
    (p : DyadicJacobiChordParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (boundary : ℕ → ℚ) (hfirst : boundary 0 = -1) (hlast : boundary N = 1)
    (R : Fin N → ℚ) (cells : Fin N → JacobiChordRangeCell K)
    (hcheck : ∀ i : Fin N, (cells i).Valid cfg productError eulerError q order p
      (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i)) :
    (combineJacobiChordCells cfg boundary cells).Contains
      (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s : ℂ)) := by
  have hb (i : Fin N) := (cells i).sound cfg productError eulerError q order hqexact hqnodes
    ht p hp hbt hba (hcheck i)
  have hout := sumBalls_contains (fun i => scale_contains (hb i).1 (boundary (i+1)-boundary i))
  have he := nonuniform_normalized_integral_sum N boundary (jacobiChordKernel t a)
    (jacobiChordKernel_continuous_real ht hq a)
  rw [he, hfirst, hlast] at hout
  simpa only [combineJacobiChordCells, Rat.cast_neg, Rat.cast_one] using hout

theorem jacobiChord_composite_contains {K N : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0 < t) (htu : t ≤ 17/20)
    (p : DyadicJacobiChordParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (boundary : ℕ → ℚ) (hfirst : boundary 0 = -1) (hlast : boundary N = 1)
    (R : Fin N → ℚ) (cells : Fin N → JacobiChordRangeCell K)
    (hcheck : ∀ i : Fin N, (cells i).Valid cfg productError eulerError q order p
      (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i)) :
    (combineJacobiChordCells cfg boundary cells).Contains
      (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s : ℂ)) :=
  jacobiChord_composite_contains_of_nome cfg productError eulerError q order hqexact hqnodes
    ht ((leftNome_lt_one_fifth ht htu).le.trans (by norm_num)) p hp hbt hba
    boundary hfirst hlast R cells hcheck

theorem jacobiChord_composite_contains_to_seven_fifths {K N : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0 < t) (htu : t ≤ 7/5)
    (p : DyadicJacobiChordParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (boundary : ℕ → ℚ) (hfirst : boundary 0 = -1) (hlast : boundary N = 1)
    (R : Fin N → ℚ) (cells : Fin N → JacobiChordRangeCell K)
    (hcheck : ∀ i : Fin N, (cells i).Valid cfg productError eulerError q order p
      (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i)) :
    (combineJacobiChordCells cfg boundary cells).Contains
      (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s : ℂ)) :=
  jacobiChord_composite_contains_of_nome cfg productError eulerError q order hqexact hqnodes
    ht (leftNome_lt_one_third ht htu).le p hp hbt hba
    boundary hfirst hlast R cells hcheck

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiChord_composite_contains
