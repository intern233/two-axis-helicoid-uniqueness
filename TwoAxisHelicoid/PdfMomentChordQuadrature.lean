import TwoAxisHelicoid.PdfComplexChordQuadrature
import TwoAxisHelicoid.QuadratureMomentError
import TwoAxisHelicoid.RationalQuadrature12
import TwoAxisHelicoid.RationalQuadrature16

namespace TwoAxisHelicoid.PdfVertical
open Complex Metric MeasureTheory

theorem twelve_point_half_disk_factor : rationalQuadrature12.momentErrorFactor 64 (1/2) ≤ 3/10^9 := by decide +kernel
theorem sixteen_point_half_disk_factor : rationalQuadrature16.momentErrorFactor 64 (1/2) ≤ 5/10^12 := by decide +kernel

def momentChordGrid {K N : ℕ} (p : ChordParams) (q : QuadratureRule K) (terms : ℕ)
    (boundary : ℕ → ℚ) (M : Fin N → ℚ) (factor : ℚ) : CGrid :=
  CGrid.finiteSum N (fun i =>
    let width := boundary (i+1)-boundary i
    let samples := weightedChordSamples p q terms (jacobiCellCenter boundary i) (jacobiCellRadius boundary i)
    (samples.add (CGrid.ofError (M i*factor))).scale (Grid.ofRats width width))

/-- Each Cauchy disk has twice the half-width of its integration segment.
The same checked rational moment factor therefore serves every segment. -/
theorem momentChordGrid_sound {K N : ℕ} {p : ChordParams} {t a : ℝ} (ps : p.Sound t a)
    (ht : 0<t) (hu : t≤7/5) (q : QuadratureRule K) (nodes : q.NodesInUnit)
    {degree : ℕ} {factor : ℚ} (coef : q.momentErrorFactor degree (1/2)≤factor) (terms : ℕ)
    (bd : ℕ → ℚ) (first : bd 0 = -1) (last : bd N = 1) (M : Fin N → ℚ)
    (widths : ∀ i : Fin N, 0<jacobiCellRadius bd i)
    (disks : ∀ i : Fin N, ChordDiskBound (jacobiCellCenter bd i) (2*jacobiCellRadius bd i) (M i) t a) :
    (momentChordGrid p q terms bd M factor).Contains
      (∫ x : ℝ in (-1)..1, jacobiChordKernel t a (x:ℂ)) := by
  have part (i : Fin N) :
      ((weightedChordSamples p q terms (jacobiCellCenter bd i) (jacobiCellRadius bd i)).add
        (CGrid.ofError (M i*factor))).Contains (normalizedIntegral (jacobiChordKernel t a)
          (jacobiCellCenter bd i:ℂ) (jacobiCellRadius bd i:ℝ)) := by
    let c := jacobiCellCenter bd i
    let h := jacobiCellRadius bd i
    have hw : 0<h := widths i
    have hr : h<2*h := by linarith
    have disk := disks i
    have diff : DifferentiableOn ℂ (jacobiChordKernel t a) (closedBall (c:ℂ) ((2*h:ℚ):ℝ)) :=
      fun z hz => (disk z hz).2.differentiableWithinAt
    have bound (z : ℂ) (hz : z∈closedBall (c:ℂ) ((2*h:ℚ):ℝ)) := (disk z hz).1
    have err := q.rational_moment_error degree nodes hw.le hr (diff.diffContOnCl_ball (fun _ hz => hz)) bound
    have ratio : h/(2*h)=1/2 := by field_simp [hw.ne']
    rw [ratio] at err
    have M0 : 0≤(M i:ℝ) := (norm_nonneg _).trans (bound _ (mem_closedBall_self (Rat.cast_nonneg.mpr (by linarith))))
    have lim : (M i*q.momentErrorFactor degree (1/2):ℚ)≤M i*factor :=
      mul_le_mul_of_nonneg_left coef (Rat.cast_nonneg.mp M0)
    have enlarged := err.trans ((Rat.cast_le (K:=ℝ)).mpr lim)
    have val := CGrid.contains_add (weightedChordSamples_sound ps ht hu q terms c h) (CGrid.contains_ofError enlarged)
    rwa [add_sub_cancel] at val
  have weighted (i : Fin N) := CGrid.contains_scale
    (Grid.contains_rats (a:=bd (i+1)-bd i) (b:=bd (i+1)-bd i) (x:=((bd (i+1)-bd i:ℚ):ℝ)) le_rfl le_rfl) (part i)
  have allBounds := CGrid.contains_finiteSum weighted
  simp only [Complex.ofReal_ratCast] at allBounds
  have eq := nonuniform_normalized_integral_sum N bd (jacobiChordKernel t a)
    (jacobiChordKernel_continuous_real ht (leftNome_lt_one_third ht hu).le a)
  rw [eq,first,last] at allBounds
  simpa only [momentChordGrid,Rat.cast_neg,Rat.cast_one] using allBounds

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.twelve_point_half_disk_factor
#print axioms TwoAxisHelicoid.PdfVertical.momentChordGrid_sound

