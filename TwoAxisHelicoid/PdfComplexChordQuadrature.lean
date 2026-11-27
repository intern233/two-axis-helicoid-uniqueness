import TwoAxisHelicoid.PdfComplexChordDisk
import TwoAxisHelicoid.PdfRefinedChordOriginal

namespace TwoAxisHelicoid.PdfVertical
open Complex Metric MeasureTheory

def weightedChordSamples {K : ℕ} (p : ChordParams) (q : QuadratureRule K) (terms : ℕ)
    (c h : ℚ) : CGrid :=
  CGrid.finiteSum K (fun j =>
    let s := c+h*q.node j
    (truncatedChordCell terms p (Grid.ofRats s s)).scale (Grid.ofRats (q.weight j) (q.weight j)))

theorem weightedChordSamples_sound {K : ℕ} {p : ChordParams} {t a : ℝ} (ps : p.Sound t a)
    (ht : 0<t) (hu : t≤7/5) (q : QuadratureRule K) (terms : ℕ) (c h : ℚ) :
    (weightedChordSamples p q terms c h).Contains (q.apply (jacobiChordKernel t a) (c:ℂ) (h:ℝ)) := by
  have point (x : ℚ) : (Grid.ofRats x x).Contains (x:ℝ) := Grid.contains_rats le_rfl le_rfl
  have weighted (j : Fin K) := CGrid.contains_scale (point (q.weight j))
    (truncatedChordCell_sound terms ps (point (c+h*q.node j)) ht hu)
  have sum := CGrid.contains_finiteSum weighted
  simpa only [weightedChordSamples, QuadratureRule.apply, Rat.cast_add, Rat.cast_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast] using sum

def diskChordCellGrid {K : ℕ} (p : ChordParams) (q : QuadratureRule K) (degree terms : ℕ)
    (c h R M : ℚ) : CGrid :=
  (weightedChordSamples p q terms c h).add (CGrid.ofError (quadratureErrorBound q degree h R M))

theorem diskChordCellGrid_sound {K : ℕ} {p : ChordParams} {t a : ℝ} (ps : p.Sound t a)
    (ht : 0<t) (hu : t≤7/5) (q : QuadratureRule K) {degree : ℕ}
    (exactness : q.ExactTo degree) (nodes : q.NodesInUnit) (terms : ℕ)
    {c h R M : ℚ} (width : 0≤h) (inside : h<R) (disk : ChordDiskBound c R M t a) :
    (diskChordCellGrid p q degree terms c h R M).Contains
      (normalizedIntegral (jacobiChordKernel t a) (c:ℂ) (h:ℝ)) := by
  have h0 := (Rat.cast_nonneg (K:=ℝ)).mpr width
  have hR := (Rat.cast_lt (K:=ℝ)).mpr inside
  have hM : 0≤(M:ℝ) := (norm_nonneg _).trans (disk _ (mem_closedBall_self (h0.trans hR.le))).1
  have diff : DifferentiableOn ℂ (jacobiChordKernel t a) (closedBall (c:ℂ) (R:ℝ)) :=
    fun z hz => (disk z hz).2.differentiableWithinAt
  have err := QuadratureRule.analytic_error_bound exactness nodes h0 hR hM
    (diff.diffContOnCl_ball (fun _ hz => hz)) (fun z hz => (disk z (sphere_subset_closedBall hz)).1)
  have remainder : ‖normalizedIntegral (jacobiChordKernel t a) (c:ℂ) (h:ℝ) -
      q.apply (jacobiChordKernel t a) (c:ℂ) (h:ℝ)‖≤(quadratureErrorBound q degree h R M:ℝ) := by
    simpa only [quadratureErrorBound,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_one,
      Rat.cast_div,Rat.cast_pow] using err
  have sum := weightedChordSamples_sound ps ht hu q terms c h
  have val := CGrid.contains_add sum (CGrid.contains_ofError remainder)
  rwa [add_sub_cancel] at val

def diskChordGrid {K N : ℕ} (p : ChordParams) (q : QuadratureRule K) (degree terms : ℕ)
    (boundary : ℕ → ℚ) (R M : Fin N → ℚ) : CGrid :=
  CGrid.finiteSum N (fun i =>
    let w := boundary (i+1)-boundary i
    (diskChordCellGrid p q degree terms (jacobiCellCenter boundary i) (jacobiCellRadius boundary i)
      (R i) (M i)).scale (Grid.ofRats w w))

theorem diskChordGrid_sound {K N : ℕ} {p : ChordParams} {t a : ℝ} (ps : p.Sound t a)
    (ht : 0<t) (hu : t≤7/5) (q : QuadratureRule K) {degree : ℕ}
    (exactness : q.ExactTo degree) (nodes : q.NodesInUnit) (terms : ℕ)
    (boundary : ℕ → ℚ) (first : boundary 0 = -1) (last : boundary N = 1) (R M : Fin N → ℚ)
    (sizes : ∀ i : Fin N, 0≤jacobiCellRadius boundary i ∧ jacobiCellRadius boundary i < R i)
    (disks : ∀ i : Fin N, ChordDiskBound (jacobiCellCenter boundary i) (R i) (M i) t a) :
    (diskChordGrid p q degree terms boundary R M).Contains
      (∫ x : ℝ in (-1)..1, jacobiChordKernel t a (x:ℂ)) := by
  have each (i : Fin N) := diskChordCellGrid_sound ps ht hu q exactness nodes terms (sizes i).1 (sizes i).2 (disks i)
  have weighted (i : Fin N) := CGrid.contains_scale
    (Grid.contains_rats (a:=boundary (i+1)-boundary i) (b:=boundary (i+1)-boundary i)
      (x:=((boundary (i+1)-boundary i:ℚ):ℝ)) le_rfl le_rfl) (each i)
  have allBounds := CGrid.contains_finiteSum weighted
  simp only [Complex.ofReal_ratCast] at allBounds
  have eq := nonuniform_normalized_integral_sum N boundary (jacobiChordKernel t a)
    (jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a)
  rw [eq, first, last] at allBounds
  simpa only [diskChordGrid,Rat.cast_neg,Rat.cast_one] using allBounds

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.diskChordGrid_sound

