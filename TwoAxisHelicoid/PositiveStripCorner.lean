import TwoAxisHelicoid.ActualLowHeightEndSide
import TwoAxisHelicoid.HeightStripPoleSide

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The upper puncture has positive transverse displacement throughout
the first-quarter positive-height strip, uniformly down to height zero. -/
theorem quarter_upper_puncture_transverse_positive {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    let P : ℂ := 1+I*t
    let W := 1/(2*(1-a))
    ∀ᶠ z in 𝓝[≠] P, z.re≤1 → X z 2-X 1 2∈Ioc (0:ℝ) W → X 1 1<X z 1 := by
  intro P W
  let H := actualComplexHeight t a 1 ht
  obtain ⟨K,R,rp,left,_,order⟩ := actual_low_height_end_transverse_order ht ha d per
  have translate : Tendsto (fun z : ℂ => z-P) (𝓝[≠] P) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun z : ℂ => z-P) P := by fun_prop
      simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.mpr hz
  have physical := actual_height_pole_left_strip (a:=a) ht W R
  have regular := rhombic_puncture_eventually_off_lattice ht
  filter_upwards [translate.eventually left,translate.eventually physical,translate.eventually regular] with z inv far off
  intro x bound
  let w := z-P
  have eq : X w=X z := by simpa [w] using (per (z-P) P (rhombicPeriodPair t ht).ω₂_mem_lattice).symm
  have height := actual_complex_height_centered_primitive ht d off
  change X w 2-X 1 2=(H w).re at height
  rw [eq] at height
  have inside : (H w).re∈Ioc (0:ℝ) W := height ▸ bound
  have wp : 0<W := inside.1.trans_le inside.2
  have fi := far (show w.re≤0 by simpa [w,P] using x) (by rw [abs_of_pos inside.1]; exact inside.2)
  change R<(H w).im at fi
  have pos := rp.trans fi
  obtain ⟨axis,positive,_⟩ := order (H w).im (by rwa [abs_of_pos pos])
  let V := fun x : ℝ => X (K ⟨x,(H w).im⟩) 1-X 1 1
  change V 0=0 at axis
  have increasing : StrictMonoOn V (Icc (-W) W) := positive pos
  have result := increasing (show (0:ℝ)∈Icc (-W) W from ⟨by linarith,wp.le⟩)
    (show (H w).re∈Icc (-W) W from ⟨by linarith [inside.1],inside.2⟩) inside.1
  rw [axis] at result
  change 0<X (K (H w)) 1-X 1 1 at result
  change K (H w)=w at inv
  rw [inv,eq] at result
  exact sub_pos.mp result

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_upper_puncture_transverse_positive
