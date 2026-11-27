import TwoAxisHelicoid.CentralBandHeightBracket
import TwoAxisHelicoid.CentralBandLeftHeightCover
import TwoAxisHelicoid.CentralBandRightHeightCover

namespace TwoAxisHelicoid
open Complex Set

theorem certified_central_height_arc_bracket :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ y∈Icc (1/8:ℝ) (3/8), ∃! x : ℝ, x∈Ioo (1/2:ℝ) (5/8) ∧ X ((x:ℂ)+I*y) 2=X 1 2 :=
  central_band_bracket_of_height_edges centralBandLeftHeightCover centralBandRightHeightCover

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_central_height_arc_bracket
