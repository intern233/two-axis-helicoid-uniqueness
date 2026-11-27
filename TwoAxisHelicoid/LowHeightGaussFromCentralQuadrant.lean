import TwoAxisHelicoid.LowSlabEarlyGauss
import TwoAxisHelicoid.LowSlabImaginaryVelocity
import TwoAxisHelicoid.LowSlabSectorRectangle
import TwoAxisHelicoid.LowSlabGaussTopSound
import TwoAxisHelicoid.LowSlabGaussTopCover
import TwoAxisHelicoid.LowSlabWestLeftCover
import TwoAxisHelicoid.LowSlabWestRightCover
import TwoAxisHelicoid.LowSlabWestBottomCover
import TwoAxisHelicoid.LowSlabWestTopCover
import TwoAxisHelicoid.LowSlabMiddleLeftCover
import TwoAxisHelicoid.LowSlabMiddleRightCover
import TwoAxisHelicoid.LowSlabMiddleBottomCover
import TwoAxisHelicoid.LowSlabMiddleTopCover
import TwoAxisHelicoid.LowSlabGateCover

namespace TwoAxisHelicoid
open Complex Set

/-- At every low positive physical height two overlapping row ranges
have strictly signed Gauss components. The second range continues to
the puncture and includes its whole upper quarter. -/
theorem low_height_gauss_signs_of_central_quadrant
    (q : let p := certifiedClosedParameters
      let H := actualComplexHeight p.t p.a 1 p.height_pos
      let G := thetaGauss p.t p.a 1
      let F := centralPhaseThetaRatio p.t p.a
      ∀ x∈Ioc (1/2:ℝ) p.a, ∀ y∈Ioc (0:ℝ) (p.t/2), let z := (x:ℂ)+I*y
        (F z).re<0 ∧ 0<(F z).im ∧ ((H z).re=0 → (G z).re<0 ∧ (G z).im<0)) :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    (∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioc (0:ℝ) (3/8) → 0<(H z).re → (G z).re<0) ∧
    ∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t → 7/32≤z.im →
      (H z).re∈Ioc (0:ℝ) (1/4) → (G z).im<0 := by
  intro p H G
  have eq (x y : ℝ) : (x:ℂ)+I*y=⟨x,y⟩ := by apply Complex.ext <;> simp
  constructor
  · apply low_slab_real_velocity_from_boundary
    · simpa using lowSlabGaussTopCover.sound
    · intro x hx y hy hit
      have v := q x ⟨hx.1,hx.2.le⟩ y ⟨hy.1,hy.2.le⟩
      rw [eq] at v
      exact (v.2.2 hit).1
  · apply low_slab_imaginary_velocity_from_sectors
    · have r := low_slab_sector_rectangle (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        lowSlabWestLeftCover lowSlabWestRightCover lowSlabWestBottomCover lowSlabWestTopCover
      norm_num at r
      exact fun x hx y hy => r x hx.1 hx.2 y hy.1 hy.2
    · have r := low_slab_sector_rectangle (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        lowSlabMiddleLeftCover lowSlabMiddleRightCover lowSlabMiddleBottomCover lowSlabMiddleTopCover
      norm_num at r
      exact fun x hx y hy => r x hx.1 hx.2 y hy.1 hy.2
    · intro y hy
      have v := lowSlabGateCover.sound y (by norm_num; exact hy)
      norm_num [LowSlabQuantity.holds,centralBandEdgePoint] at v
      exact v
    · intro x hx y hy
      have v := q x hx y hy
      rw [eq] at v
      exact ⟨v.1,v.2.1.le⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_height_gauss_signs_of_central_quadrant
