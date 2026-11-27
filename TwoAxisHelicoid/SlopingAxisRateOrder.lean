import TwoAxisHelicoid.SlopingDerivativeTraceSound
import TwoAxisHelicoid.SlopingScalarEnvelope
import TwoAxisHelicoid.TraceDataSlopingSpatialCover
import TwoAxisHelicoid.TraceDataCentralDisplacementCover
import TwoAxisHelicoid.OriginalPeriodAnalytic

namespace TwoAxisHelicoid
open Complex Set

/-- A positive imaginary derivative for the two reflected theta
contributions gives an actual strict increase from the axis, including
arbitrarily small positive parameters where the first derivative is zero
at the endpoint itself. -/
theorem sloping_transverse_strict_near_axis {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (acc : CheckedSlopingPositiveAcceleration (-3/16) (3/16)) :
    StrictMonoOn (fun s => X (originalPeriodPath t s) 1) (Icc (0:ℝ) (3/16)) := by
  let v : ℂ := (1-I*t)/2
  let A := fun s : ℝ => thetaA t a (originalPeriodPath t s)
  let D := fun s : ℝ => deriv (thetaA t a) (originalPeriodPath t s)
  let h := fun s : ℝ => (-(v*A s)).im
  have positive (s : ℝ) (hs : s∈Icc (-3/16:ℝ) (3/16)) : 0<(-v^2*D s).im := by
    apply acc.sound ht ha s
    simpa only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] using hs
  have dh (s : ℝ) (hs : s∈Icc (-3/16:ℝ) (3/16)) : HasDerivAt h (-v^2*D s).im s := by
    have off := originalPath_regular hp (s:=s) ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have da := (thetaA_differentiableAt hp a off).hasDerivAt.comp s (originalPeriodPath_hasDerivAt t s)
    have deriv := imCLM.hasFDerivAt.comp_hasDerivAt s (da.const_mul v).neg
    convert deriv using 1
    · rfl
    · change (-v^2*D s).im=(-(v*(D s*v))).im
      congr 1
      ring
  have mono : StrictMonoOn h (Icc (-3/16:ℝ) (3/16)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun s hs => (dh s hs).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(dh s (Ioo_subset_Icc_self hs)).deriv]
    exact positive s (Ioo_subset_Icc_self hs)
  have df (s : ℝ) (hs : s∈Icc (0:ℝ) (3/16)) := sloping_transverse_spatial_derivative hp d (s:=s)
    ⟨hs.1,by linarith [hs.2]⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun s hs => (df s hs).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Icc] at hs
  rw [(df s (Ioo_subset_Icc_self hs)).deriv]
  have order := mono (a:= -s) (b:=s) ⟨by linarith [hs.2],by linarith [hs.1]⟩
    ⟨by linarith [hs.1],hs.2.le⟩ (by linarith [hs.1])
  change (-(v*A (-s))).im<(-(v*A s)).im at order
  change 0< -(v*(A s-A (-s))).im/2
  rw [mul_sub,sub_im]
  simp only [neg_im] at order
  linarith

/-- Every nonzero positive parameter of the full sloping half cycle
has strictly positive transverse displacement from its starting point. -/
theorem sloping_transverse_positive_on_half {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (acc : CheckedSlopingPositiveAcceleration (-3/16) (3/16)) :
    ∀ s∈Ioc (0:ℝ) 1, X (originalPeriodPath t 0) 1<X (originalPeriodPath t s) 1 := by
  let f := fun s => X (originalPeriodPath t s) 1
  have df (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt f (slopingTransverseRate t a s) s :=
    sloping_transverse_spatial_derivative hp d hs
  have small := sloping_transverse_strict_near_axis ht ha hp d acc
  have Y15 := TraceData.slopingSecondSpan15.sound ht ha df
  have tail := TraceData.slopingSecondSpan56.sound ht ha df
  have total := TraceData.central_half_period_displacement_cover.sound ht ha df
  norm_num at Y15 tail total
  have mid : StrictMonoOn f (Icc (3/16:ℝ) (225/256)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (df s ⟨by linarith [hs.1],by linarith [hs.2]⟩).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    have b := (Y15.rates s (Ioo_subset_Icc_self hs)).1
    rw [(df s ⟨by linarith [hs.1],by linarith [hs.2]⟩).deriv]
    norm_num at b
    linarith
  intro s hs
  change f 0<f s
  by_cases low : s≤3/16
  · exact small (by norm_num [mem_Icc]) ⟨hs.1.le,low⟩ hs.1
  by_cases high : 225/256≤s
  · have b := (tail.part s 1 high hs.2 le_rfl).2
    norm_num at b
    linarith [total.1]
  · exact (small (a:=0) (b:=3/16) (by norm_num [mem_Icc]) (by norm_num [mem_Icc]) (by norm_num)).trans
      (mid (by norm_num [mem_Icc]) ⟨le_of_not_ge low,le_of_not_ge high⟩ (lt_of_not_ge low))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_transverse_positive_on_half
