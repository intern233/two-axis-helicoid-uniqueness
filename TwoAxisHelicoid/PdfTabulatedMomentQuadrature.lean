import TwoAxisHelicoid.PdfMomentChordQuadrature

namespace TwoAxisHelicoid.PdfVertical

def chordMomentArgument {K : ℕ} (q : QuadratureRule K) (bd : ℕ → ℚ) (i : ℕ) (j : Fin K) : Grid :=
  let s := jacobiCellCenter bd i + jacobiCellRadius bd i * q.node j
  Grid.ofRats s s

def tabulatedMomentChordGrid {K N : ℕ} (values : Fin N → Fin K → CGrid)
    (weights : Fin K → Grid) (bd : ℕ → ℚ) (M : Fin N → ℚ) (factor : ℚ) : CGrid :=
  CGrid.finiteSum N (fun i =>
    let width := bd (i+1)-bd i
    let samples := CGrid.finiteSum K (fun j => (values i j).scale (weights j))
    (samples.add (CGrid.ofError (M i*factor))).scale (Grid.ofRats width width))

/-- Exact finite sample and weight tables can be checked independently for
each segment. Substitution preserves the entire complex quadrature box. -/
theorem momentChordGrid_eq_tabulated {K N : ℕ} (p : ChordParams) (q : QuadratureRule K)
    (terms : ℕ) (bd : ℕ → ℚ) (M : Fin N → ℚ) (factor : ℚ) (points : Fin N → Fin K → Grid)
    (weights : Fin K → Grid) (values : Fin N → Fin K → CGrid)
    (point_eq : ∀ (i : Fin N) (j : Fin K), chordMomentArgument q bd i j=points i j)
    (weight_eq : ∀ j : Fin K, Grid.ofRats (q.weight j) (q.weight j)=weights j)
    (value_eq : ∀ (i : Fin N) (j : Fin K), truncatedChordCell terms p (points i j)=values i j) :
    momentChordGrid p q terms bd M factor=tabulatedMomentChordGrid values weights bd M factor := by
  have sums (i : Fin N) : weightedChordSamples p q terms (jacobiCellCenter bd i) (jacobiCellRadius bd i)
      = CGrid.finiteSum K (fun j => (values i j).scale (weights j)) := by
    apply congrArg (CGrid.finiteSum K)
    funext j
    change (truncatedChordCell terms p (chordMomentArgument q bd i j)).scale
      (Grid.ofRats (q.weight j) (q.weight j)) = (values i j).scale (weights j)
    rw [point_eq i j,weight_eq j,value_eq i j]
  unfold momentChordGrid tabulatedMomentChordGrid
  apply congrArg (CGrid.finiteSum N)
  funext i
  dsimp only
  rw [sums i]

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.momentChordGrid_eq_tabulated

