import TwoAxisHelicoid.CertifiedQuarterHeightRows
import TwoAxisHelicoid.LowSlabGaussPhase
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set

/-- Two compact theta sectors control the entire second portion of a
low positive level, up to and including points arbitrarily close to
the end. The upper half is turned onto the negative-height half-tile. -/
theorem low_slab_imaginary_velocity_from_sectors :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let F := centralPhaseThetaRatio p.t p.a
    let G := thetaGauss p.t p.a 1
    let sector := fun z : ℂ => ∀ q : ℝ, |q|≤1 → 4*(F z).re+q*(F z).im<0
    (∀ x∈Icc (0:ℝ) (1/2), ∀ y∈Icc (0:ℝ) (7/16), sector ⟨x,y⟩) →
    (∀ x∈Icc (1/2:ℝ) (11/16), ∀ y∈Icc (7/32:ℝ) (7/16), sector ⟨x,y⟩) →
    (∀ y∈Icc (7/32:ℝ) (7/16), 1/4<(H ⟨11/16,y⟩).re) →
    (∀ x∈Ioc (1/2:ℝ) p.a, ∀ y∈Ioc (0:ℝ) (p.t/2), (F ⟨x,y⟩).re<0 ∧ 0≤(F ⟨x,y⟩).im) →
    ∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t → 7/32≤z.im →
      (H z).re∈Ioc (0:ℝ) (1/4) → (G z).im<0 := by
  intro p H F G sector west middle gate quadrant z hx hy early hit
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  obtain ⟨rows,zeros⟩ := certified_quarter_height_row_order
  have top : p.t/2≤7/16 := by have b := certifiedClosedParameters_bounds.1.2; norm_num [rootTUpper] at b; linarith
  have lower := (by norm_num [rootTLower] : (43/50:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have low := (by norm_num [rootALower] : (29/50:ℝ)<rootALower).trans certifiedClosedParameters_bounds.2.1
  have fromSector (w : ℂ) := low_slab_gauss_imag_negative (z:=w) p.height_pos p.abscissa_mem low.le p.vertical_closed
  have within {x : ℝ} (h : x∈Icc (1/2:ℝ) p.a) : x∈Icc (0:ℝ) 1 :=
    ⟨by linarith [h.1],h.2.trans p.abscissa_mem.2.le⟩
  by_cases small : z.im≤p.t/2
  · obtain ⟨v,hv,zero⟩ := zeros z.im ⟨hy.1,small⟩
    have inc := rows z.im hy
    have vx := (inc.lt_iff_lt (within hv) hx).mp (zero.trans_lt hit.1)
    have zz : z.im∈Icc (7/32:ℝ) (7/16) := ⟨early,small.trans top⟩
    have xr := (inc.lt_iff_lt hx (show (11/16:ℝ)∈Icc 0 1 by norm_num)).mp (hit.2.trans_lt (gate z.im zz))
    exact fromSector z (by rw [abs_of_pos hit.1]; exact hit.2) (Or.inl (middle _ ⟨hv.1.trans vx.le,xr.le⟩ _ zz))
  · let w : ℂ := -z+(1+I*p.t)
    have wx : w.re=1-z.re := by simp [w]; ring
    have wy : w.im=p.t-z.im := by simp [w]; ring
    have xx : w.re∈Icc (0:ℝ) 1 := by rw [wx]; constructor <;> linarith [hx.1,hx.2]
    have yy : w.im∈Ioc (0:ℝ) (p.t/2) := by rw [wy]; constructor <;> linarith [hy.2,not_le.mp small]
    have yt : w.im∈Ioo (0:ℝ) p.t := ⟨yy.1,yy.2.trans_lt (half_lt_self p.height_pos)⟩
    have oz := rhombic_horizontal_strip_not_mem (z:=z) p.height_pos hy
    have ow := rhombic_horizontal_strip_not_mem (z:=w) p.height_pos yt
    have val : (H w).re= -(H z).re := by
      rw [← actual_complex_height_centered_primitive p.height_pos d ow,
        ← actual_complex_height_centered_primitive p.height_pos d oz,
        show X w=X (-z) from per (-z) _ (rhombicPeriodPair p.t p.height_pos).ω₂_mem_lattice]
      exact congrFun (explicit_centered_primitive_reflections p.height_pos d per z oz).1 2
    apply (quarter_gauss_halfturn_imag (a:=p.a) lower.le p.height_pos hy).mp
    change (G w).im<0
    apply fromSector w (by rw [val,abs_neg,abs_of_pos hit.1]; exact hit.2)
    by_cases cut : w.re≤1/2
    · exact Or.inl (west _ ⟨xx.1,cut⟩ _ ⟨yy.1.le,yy.2.trans top⟩)
    · obtain ⟨v,hv,zero⟩ := zeros w.im yy
      have neg : (H w).re<0 := val.trans_lt (neg_lt_zero.mpr hit.1)
      have comp := ((rows w.im yt).lt_iff_lt xx (within hv)).mp (neg.trans_eq zero.symm)
      exact Or.inr ⟨neg.le,quadrant _ ⟨not_le.mp cut,comp.le.trans hv.2⟩ _ yy⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_imaginary_velocity_from_sectors
