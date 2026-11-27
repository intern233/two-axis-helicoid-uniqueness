import TwoAxisHelicoid.PdfQuadratureNodeGrid

namespace TwoAxisHelicoid.PdfVertical
open Complex ComplexBall Metric MeasureTheory

/-- The complex disk certificate bounds the quadrature remainder independently of the
particular enclosures used at the real nodes. Both may therefore be refined separately. -/
theorem chord_cell_quadrature_error {K : ℕ} (cfg : BallConfig) {productError eulerError : ℕ}
    (q : QuadratureRule K) {order : ℕ} (exactness : q.ExactTo order) (nodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0<t) {p : DyadicJacobiChordParameters} (hp : p.Valid cfg productError)
    (bt : (p.base.base.height.toBall cfg.prec).Contains (t:ℂ))
    (ba : (p.base.base.abscissa.toBall cfg.prec).Contains (a:ℂ))
    {x h R : ℚ} {w : JacobiChordRangeCell K}
    (valid : w.Valid cfg productError eulerError q order p x h R) :
    ‖normalizedIntegral (jacobiChordKernel t a) (x:ℂ) (h:ℝ) -
      q.apply (jacobiChordKernel t a) (x:ℂ) (h:ℝ)‖ ≤
      (quadratureErrorBound q order h R (w.diskBound cfg) : ℝ) := by
  obtain ⟨nonneg,radius,center,disk,trace,_,_⟩ := valid
  have centerBound := coarsen_contains (rational_contains x) center
  have point (z : ℂ) (hz : z ∈ closedBall (x:ℂ) (R:ℝ)) :=
    w.diskFunction.sound cfg productError eulerError ht p hp w.disk bt ba
      (coarsen_contains (inflate_contains centerBound (mem_closedBall_iff_norm.mp hz)) disk) trace
  have bound (z : ℂ) (hz : z ∈ closedBall (x:ℂ) (R:ℝ)) :
      ‖jacobiChordKernel t a z‖ ≤ (w.diskBound cfg : ℝ) := DyadicBall.norm_le_normUpper (point z hz).1
  have diff : DifferentiableOn ℂ (jacobiChordKernel t a) (closedBall (x:ℂ) (R:ℝ)) :=
    fun z hz => (point z hz).2.differentiableWithinAt
  have h0 : (0:ℝ)≤h := Rat.cast_nonneg.mpr nonneg
  have hR : (h:ℝ)<R := Rat.cast_lt.mpr radius
  have hM := (norm_nonneg _).trans (bound _ (mem_closedBall_self (h0.trans hR.le)))
  have err := QuadratureRule.analytic_error_bound exactness nodes h0 hR hM
    (diff.diffContOnCl_ball (fun _ hz => hz)) (fun z hz => bound z (sphere_subset_closedBall hz))
  simpa only [quadratureErrorBound,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_sub] using err

def refinedChordQuadratureCell {K : ℕ} (cfg : BallConfig) (q : QuadratureRule K) (order terms : ℕ)
    (p : ChordParams) (x h R : ℚ) (w : JacobiChordRangeCell K) (selected : Fin K → Bool) : CGrid :=
  (CGrid.finiteSum K (fun j => refinedWeightedChordNode terms p (x+h*q.node j) (q.weight j)
    ((w.nodes j).output.toBall cfg.prec) (selected j))).add
      (CGrid.ofError (quadratureErrorBound q order h R (w.diskBound cfg)))

theorem refinedChordQuadratureCell_sound {K : ℕ} (cfg : BallConfig) {productError eulerError : ℕ}
    (q : QuadratureRule K) {order : ℕ} (exactness : q.ExactTo order) (nodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0<t) (hu : t≤7/5) {old : DyadicJacobiChordParameters} (hp : old.Valid cfg productError)
    (bt : (old.base.base.height.toBall cfg.prec).Contains (t:ℂ))
    (ba : (old.base.base.abscissa.toBall cfg.prec).Contains (a:ℂ))
    {p : ChordParams} (ps : p.Sound t a) (terms : ℕ) {x h R : ℚ} {w : JacobiChordRangeCell K}
    (valid : w.Valid cfg productError eulerError q order old x h R) (selected : Fin K → Bool) :
    (refinedChordQuadratureCell cfg q order terms p x h R w selected).Contains
      (normalizedIntegral (jacobiChordKernel t a) (x:ℂ) (h:ℝ)) := by
  have err := chord_cell_quadrature_error cfg q exactness nodes ht hp bt ba valid
  have center := coarsen_contains (rational_contains x) valid.2.2.1
  have weighted (j : Fin K) := (w.nodes j).sound cfg productError eulerError ht old hp bt ba
    w.center x h (q.node j) (q.weight j) center (valid.2.2.2.2.2.1 j)
  have node (j : Fin K) := refinedWeightedChordNode_sound terms ps ht hu (x+h*q.node j) (q.weight j)
    (selected j) (by simpa only [Rat.cast_add,Rat.cast_mul] using weighted j)
  have summed := CGrid.contains_finiteSum node
  simp only [Rat.cast_add,Rat.cast_mul] at summed
  change CGrid.Contains _ (q.apply (jacobiChordKernel t a) (x:ℂ) (h:ℝ)) at summed
  have out := CGrid.contains_add summed (CGrid.contains_ofError err)
  rwa [add_sub_cancel] at out

def refinedChordQuadrature {K N : ℕ} (cfg : BallConfig) (q : QuadratureRule K) (order terms : ℕ)
    (p : ChordParams) (boundary : ℕ → ℚ) (R : Fin N → ℚ) (cells : Fin N → JacobiChordRangeCell K)
    (selected : Fin N → Fin K → Bool) : CGrid :=
  CGrid.finiteSum N (fun i =>
    let width := boundary (i+1)-boundary i
    (refinedChordQuadratureCell cfg q order terms p (jacobiCellCenter boundary i) (jacobiCellRadius boundary i)
      (R i) (cells i) (selected i)).scale (Grid.ofRats width width))

theorem refinedChordQuadrature_sound {K N : ℕ} (cfg : BallConfig) {productError eulerError : ℕ}
    (q : QuadratureRule K) {order : ℕ} (exactness : q.ExactTo order) (nodes : q.NodesInUnit)
    {t a : ℝ} (ht : 0<t) (hu : t≤7/5) {old : DyadicJacobiChordParameters} (hp : old.Valid cfg productError)
    (bt : (old.base.base.height.toBall cfg.prec).Contains (t:ℂ))
    (ba : (old.base.base.abscissa.toBall cfg.prec).Contains (a:ℂ))
    {p : ChordParams} (ps : p.Sound t a) (terms : ℕ)
    (boundary : ℕ → ℚ) (first : boundary 0 = -1) (last : boundary N = 1)
    (R : Fin N → ℚ) (cells : Fin N → JacobiChordRangeCell K)
    (valid : ∀ i, (cells i).Valid cfg productError eulerError q order old
      (jacobiCellCenter boundary i) (jacobiCellRadius boundary i) (R i))
    (selected : Fin N → Fin K → Bool) :
    (refinedChordQuadrature cfg q order terms p boundary R cells selected).Contains
      (∫ s : ℝ in (-1)..1, jacobiChordKernel t a (s:ℂ)) := by
  have piece (i : Fin N) := refinedChordQuadratureCell_sound cfg q exactness nodes ht hu hp bt ba
    ps terms (valid i) (selected i)
  have scaled (i : Fin N) := CGrid.contains_scale
    (Grid.contains_rats (a:=boundary (i+1)-boundary i) (b:=boundary (i+1)-boundary i)
      (x:=((boundary (i+1)-boundary i:ℚ):ℝ)) le_rfl le_rfl) (piece i)
  have val := CGrid.contains_finiteSum scaled
  simp only [Complex.ofReal_ratCast] at val
  have whole := nonuniform_normalized_integral_sum N boundary (jacobiChordKernel t a)
    (jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a)
  rw [whole,first,last] at val
  simpa only [refinedChordQuadrature,Rat.cast_neg,Rat.cast_one] using val

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.refinedChordQuadrature_sound

