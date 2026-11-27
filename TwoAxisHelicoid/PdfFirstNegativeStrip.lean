import TwoAxisHelicoid.PdfShortNegativeStrip000

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- The first eight original rectangles have a common uniform strip bound. -/
theorem first_negative_strip_edges {t a : ℝ} (tl : ((9/10):ℝ)≤t) (tu : t≤((37/40):ℝ)) (al : ((996784061054281/1649267441664000):ℝ)≤a) (au : a≤((1013896185976057/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(10^7:ℝ) := by
  intro z hr hi
  exact (shortNegativeStrip000Bound tl tu al au z hr hi).trans (by norm_num)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.first_negative_strip_edges
