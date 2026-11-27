import TwoAxisHelicoid.CentralBandSpatialConclusion
import TwoAxisHelicoid.CentralBandLeftHeightCover
import TwoAxisHelicoid.CentralBandRightHeightCover
import TwoAxisHelicoid.CentralBandLeftGaussCover
import TwoAxisHelicoid.CentralBandRightGaussCover
import TwoAxisHelicoid.CentralBandBottomGaussCover
import TwoAxisHelicoid.CentralBandTopGaussCover

namespace TwoAxisHelicoid
open Complex Set

/-- The actual certified torus has a spatially injective height band
across the explicit parameter rectangle. In particular every central
and nearby section crossing this rectangle has two strictly monotone
horizontal coordinates on the full interval from 1/8 to 3/8. -/
theorem certified_central_rectangle_and_height_band :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let J := Icc (1/8:ℝ) (3/8)
    let K := Icc (1/2:ℝ) (5/8)
    (∀ z : ℂ, z.re∈K → z.im∈J → (G z).re≤ -(1/512) ∧ (G z).im≤ -(1/512)) ∧
    ∃ ε : ℝ, 0<ε ∧
      (∀ s : ℝ, |s|<ε → ∃ r : ℝ → ℝ, ContinuousOn r J ∧
        (∀ y∈J, r y∈Ioo (1/2:ℝ) (5/8) ∧ (H ((r y:ℂ)+I*y)).re=s) ∧
          StrictAntiOn (fun y => X ((r y:ℂ)+I*y) 0) J ∧ StrictMonoOn (fun y => X ((r y:ℂ)+I*y) 1) J) ∧
      InjOn X {z | z.re∈K ∧ z.im∈J ∧ |(H z).re|<ε} :=
  central_band_spatial_conclusion centralBandLeftHeightCover centralBandRightHeightCover centralBandLeftGaussCover
    centralBandRightGaussCover centralBandBottomGaussCover centralBandTopGaussCover

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_central_rectangle_and_height_band
