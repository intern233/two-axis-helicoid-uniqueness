import TwoAxisHelicoid.DyadicJacobiFastKernel
import TwoAxisHelicoid.JacobiRangeComposite
namespace TwoAxisHelicoid
open Complex ComplexBall Metric MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] thetaA
namespace JacobiRangeNode
def FastValid (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) : Prop :=
  (w.point.toBall cfg.prec).coarsens
    (ComplexBall.add (center.toBall cfg.prec) (ComplexBall.rational (h*node))) ∧
  w.function.FastValid cfg productError eulerError right p w.point ∧
  w.weighted.Valid cfg (dyadicInputList [w.function.output])
    (.mul (.rational weight) (.input 0))

instance (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (p : DyadicJacobiParameters) (center : DyadicBall) (h node weight : ℚ)
    (w : JacobiRangeNode) : Decidable (w.FastValid cfg productError eulerError right p center h node weight) := by
  unfold FastValid
  infer_instance

theorem fast_sound (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (center : DyadicBall) (x h node weight : ℚ)
    (hcenter : (center.toBall cfg.prec).Contains (x : ℂ))
    (w : JacobiRangeNode) (hw : w.FastValid cfg productError eulerError right p center h node weight) :
    (w.output.toBall cfg.prec).Contains ((weight : ℂ)*
      thetaA t a (((x : ℂ)+(h : ℂ)*(node : ℂ))+I*((t/2 : ℝ) : ℂ))) := by
  have hz := coarsen_contains (add_contains hcenter (rational_contains (h*node))) hw.1
  simp only [Rat.cast_mul] at hz
  have hlat : ((x : ℂ)+(h : ℂ)*(node : ℂ))+I*((t/2 : ℝ) : ℂ) ∉
      (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast] using
      rhombic_midline_not_mem ht ((x : ℝ)+(h : ℝ)*(node : ℝ))
  have hf := w.function.fast_sound cfg productError eulerError right ht ha0 ha1 hlat p hp
    w.point hbt hba hz hw.2.1
  have he := dyadicInputList_contains (.cons hf .nil)
  have hout := w.weighted.sound cfg _ _ he _ hw.2.2
  simpa only [output, BallExpression.value, BallExpression.value_rational,
    complexInputList, List.getElem?_cons_zero, Option.getD_some] using hout

end JacobiRangeNode
namespace JacobiRangeCell
def FastValid {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiParameters)
    (tlo x h R : ℚ) (w : JacobiRangeCell K) : Prop :=
  0 ≤ h ∧ h < R ∧ JacobiDiskGuard tlo x R ∧
  (w.center.toBall cfg.prec).coarsens (ComplexBall.rational x) ∧
  (w.disk.toBall cfg.prec).coarsens ((w.center.toBall cfg.prec).inflate R) ∧
  w.diskFunction.Valid cfg productError eulerError right p w.disk ∧
  (∀ i : Fin K, (w.nodes i).FastValid cfg productError eulerError right p w.center h (q.node i) (q.weight i)) ∧
  (w.output.toBall cfg.prec).coarsens
    ((sumBalls (fun i => ((w.nodes i).output.toBall cfg.prec))).inflate
      (quadratureErrorBound q order h R (w.diskBound cfg)))

instance {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (p : DyadicJacobiParameters)
    (tlo x h R : ℚ) (w : JacobiRangeCell K) :
    Decidable (w.FastValid cfg productError eulerError right q order p tlo x h R) := by
  unfold FastValid
  infer_instance

theorem fast_sound {K : ℕ} (cfg : BallConfig) (productError eulerError : ℕ) (right : Bool)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo x h R : ℚ} {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (htl : (tlo : ℝ) ≤ t) (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (w : JacobiRangeCell K) (hw : w.FastValid cfg productError eulerError right q order p tlo x h R) :
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
    (fun i => (w.nodes i).fast_sound cfg productError eulerError right ht ha0 ha1 p hp hbt hba
      w.center x h (q.node i) (q.weight i) hcenter' (hnodes i)) hout, han⟩

end JacobiRangeCell
theorem jacobi_fast_composite_contains {K N : ℕ} (cfg : BallConfig) (productError eulerError : ℕ)
    (q : QuadratureRule K) (order : ℕ) (hqexact : q.ExactTo order) (hqnodes : q.NodesInUnit)
    {tlo : ℚ} {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (htl : (tlo : ℝ) ≤ t) (p : DyadicJacobiParameters) (hp : p.Valid cfg productError)
    (hbt : (p.base.height.toBall cfg.prec).Contains (t : ℂ))
    (hba : (p.base.abscissa.toBall cfg.prec).Contains (a : ℂ))
    (boundary : ℕ → ℚ) (hfirst : boundary 0 = -1/2) (hlast : boundary N = 1/2)
    (R : Fin N → ℚ) (right : Fin N → Bool) (cells : Fin N → JacobiRangeCell K)
    (hcheck : ∀ i : Fin N, (cells i).FastValid cfg productError eulerError (right i) q order p
      tlo (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i)) :
    (combineJacobiCells cfg boundary cells).Contains
      (∫ u : ℝ in (-1/2)..(1/2), thetaA t a ((u : ℂ)+I*((t/2 : ℝ) : ℂ))) := by
  have hb (i : Fin N) := (cells i).fast_sound cfg productError eulerError (right i) q order
    hqexact hqnodes ht ha0 ha1 htl p hp hbt hba (hcheck i)
  have hout := sumBalls_contains (fun i => scale_contains (hb i).1 (boundary (i+1)-boundary i))
  have he := nonuniform_normalized_integral_sum N boundary
    (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ))) (horizontal_integrand_continuous ht a)
  rw [he] at hout
  rw [hfirst, hlast] at hout
  simpa only [combineJacobiCells, Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] using hout

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jacobi_fast_composite_contains
