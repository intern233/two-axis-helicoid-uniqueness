import TwoAxisHelicoid.QuarterSpatialLineData

namespace TwoAxisHelicoid

/-- Store an exact rational normal form for each of the two rate
bounds and the two accumulated displacement bounds of a block. -/
theorem CheckedQuarterSpatialLine.cast_bounds {f d v e l r a b L U a' b' L' U'}
    (cert : CheckedQuarterSpatialLine f d v e l r a b L U)
    (lo : a=a') (hi : b=b') (sumLo : L=L') (sumHi : U=U') :
    CheckedQuarterSpatialLine f d v e l r a' b' L' U' := by
  subst a' b' L' U'
  exact cert

end TwoAxisHelicoid
