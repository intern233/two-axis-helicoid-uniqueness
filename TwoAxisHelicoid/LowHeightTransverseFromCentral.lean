import TwoAxisHelicoid.CertifiedQuarterHeightExterior
import TwoAxisHelicoid.CertifiedCentralHalfPeriods
import TwoAxisHelicoid.CentralArcSpatialCriterion
import TwoAxisHelicoid.CalibratedQuarterBoundary
import TwoAxisHelicoid.QuarterHarmonicHeightBand

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Between the central plane and relative physical height one quarter
the open first-quarter arc stays strictly on one transverse side of
the marked vertical axis. -/
theorem low_height_transverse_of_central_injectivity (center :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2}) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t →
      X z 2-X 1 2∈Ioc (0:ℝ) (1/4) → X 1 1<X z 1 := by
  intro p X
  let L := certifiedPeriodPair
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (geom.2.2.2 z hz).1
  have per := geom.1
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
  have simple : InjOn Y {q | Y q 2=X 1 2} := fun _ hu _ hv same =>
    center hu hv (congrArg coordinateToEuclidean same)
  let m : ℂ := (1+I*p.t)/2
  have mark := certified_central_half_periods_separated.1
  change 1/2<X m 1-X 1 1 at mark
  have above : X 1 1<X m 1 := by linarith
  obtain ⟨r,inside,_,_,_,on,criterion⟩ := actual_central_spatial_embedding_test p.height_pos p.abscissa_mem d per above
  have central := (criterion.mp simple).2
  have aLow : 1/2≤p.a := (by norm_num [rootALower] : (1/2:ℝ)<rootALower).le.trans certifiedClosedParameters_bounds.2.1.le
  have bounds := transverse_boundary_height_bounds aLow p.abscissa_mem.2
  have direction := oblique_torus_direction_from_tile p.height_pos p.abscissa_mem p.vertical_closed d per certified_oblique_theta_tile
  have top := calibrated_quarter_transverse_positive p.height_pos p.abscissa_mem aLow p.vertical_closed d per
    (fun z hz => (direction z hz).1)
  have hm : m∉L.lattice := rhombic_horizontal_strip_not_mem p.height_pos (by
    change m.im∈Ioo 0 p.t
    have im : m.im=p.t/2 := by simp [m]
    rw [im]
    exact ⟨half_pos p.height_pos,half_lt_self p.height_pos⟩)
  have propagate := quarter_harmonic_height_band p.height_pos p.abscissa_mem bounds.2.le d per
    (fun z hz => ((geom.2.2.1 z hz).sub (harmonicAt_const (X 1))).comp_CLM
      (ContinuousLinearMap.proj 1 : (Fin 3 → ℝ) →L[ℝ] ℝ)) ⟨m,hm,above.ne'⟩ (by
      intro z hx hy level
      have eq : (z.re:ℂ)+I*z.im=z := by apply Complex.ext <;> simp
      rcases level with zero|calibrated
      · have id := (actual_quarter_height_row_strictMono p.height_pos hy d).injOn (Ioo_subset_Icc_self hx)
          (Ioo_subset_Icc_self (inside z.im hy)) (by rw [eq,zero]; exact (on z.im hy).symm)
        have val := central z.im hy
        change X 1 1<X ((r z.im:ℂ)+I*z.im) 1 at val
        rw [← id,eq] at val
        exact val.le
      · have val := top z.re hx z.im hy (by rwa [eq])
        rw [eq] at val
        exact val.le)
  intro z hx hy low
  exact propagate z hx hy ⟨low.1,low.2.trans_lt bounds.1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_height_transverse_of_central_injectivity
