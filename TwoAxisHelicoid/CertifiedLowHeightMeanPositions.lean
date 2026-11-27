import TwoAxisHelicoid.LowHeightSpatialComparisons
import TwoAxisHelicoid.LowHeightDisplacementsFromMeans
import TwoAxisHelicoid.QuarterSpatialEarlyLeftCover
import TwoAxisHelicoid.QuarterSpatialEarlyRightCover
import TwoAxisHelicoid.QuarterSpatialEarlyBottomCover
import TwoAxisHelicoid.QuarterSpatialEarlyTopCover
import TwoAxisHelicoid.QuarterSpatialMiddleLeftCover
import TwoAxisHelicoid.QuarterSpatialMiddleRightCover
import TwoAxisHelicoid.QuarterSpatialMiddleBottomCover
import TwoAxisHelicoid.QuarterSpatialMiddleTopCover
import TwoAxisHelicoid.QuarterSpatialLateHorizontalCover
import TwoAxisHelicoid.QuarterSpatialEarlyRowSignCover
import TwoAxisHelicoid.SpatialMeanEarlyCover
import TwoAxisHelicoid.SpatialMeanLowerCover
import TwoAxisHelicoid.SpatialMeanUpperCover
import TwoAxisHelicoid.SpatialMeanLateCover

namespace TwoAxisHelicoid
open Complex Set

/-- The spatial comparisons throughout the low-height windows, using the twelve-node quadrature formula on opposite parameter segments. -/
theorem certified_low_height_window_positions_by_means :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let P := fun z : ℂ => X z 0-X 1 0
    let Y := fun z : ℂ => X z 1-X 1 1
    (∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), 0≤P ⟨x,y⟩) ∧
    (∀ x∈Icc (9/16:ℝ) 1, Y ⟨x,7/32⟩≤5/4) ∧
    (∀ x∈Icc (15/32:ℝ) (3/5), ∀ y∈Icc (3/8:ℝ) (1/2), 5/4<Y ⟨x,y⟩) ∧
    ∀ x∈Icc (15/32:ℝ) (3/5), P ⟨x,1/2⟩<0 :=
  low_height_window_positions_of_displacements
    quarterSpatialEarlyLeftCover
    quarterSpatialEarlyRightCover
    quarterSpatialEarlyBottomCover
    quarterSpatialEarlyTopCover
    quarterSpatialMiddleLeftCover
    quarterSpatialMiddleRightCover
    quarterSpatialMiddleBottomCover
    quarterSpatialMiddleTopCover
    quarterSpatialLateHorizontalCover
    (low_height_displacements_of_means quarterSpatialEarlyRowSignCover spatialMeanEarlyCover spatialMeanLowerCover spatialMeanUpperCover spatialMeanLateCover)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_height_window_positions_by_means
