import TwoAxisHelicoid.PlaneGradientTranslations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter Metric InnerProductSpace
open scoped ContDiff NNReal RealInnerProductSpace

private theorem smooth_compact_increment {f : ℂ → ℝ} (sf : ContDiff ℝ ∞ f) {a : ℝ}
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, f z=a) :
    ∃ L : ℝ≥0, ∀ z t : ℂ, |f z-f (z+t)| ≤ (L:ℝ)*‖t‖ := by
  let g := fun z => f z-a
  have compact : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact hk
    intro z hz
    by_contra h
    exact hz (sub_eq_zero.mpr (off z h))
  obtain ⟨L,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact (sf.sub contDiff_const) (by simp)
  refine ⟨L,fun z t => ?_⟩
  have h := lip.dist_le_mul z (z+t)
  simpa [g,Real.dist_eq,dist_eq_norm] using h

/-- The operator discrepancy between translating the actual flux first and
translating the field first is bounded by |t| on every square integrable input. -/
theorem smooth_conductivity_translation_commutator {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1)
    (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ))
    (acts : ∀ w, ⇑(T w) =ᵐ[volume] (fun z => planeMetricFlux A B C z (w z))) :
    ∃ L : ℝ, 0≤L ∧ ∀ (t : ℂ) (w : Lp ℂ 2 (volume:Measure ℂ)),
      ‖T (planeFieldTranslate t w)-planeFieldTranslate t (T w)‖ ≤ L*‖t‖*‖w‖ := by
  obtain ⟨a,da⟩ := smooth_compact_increment sa hk (fun z hz => (off z hz).1)
  obtain ⟨b,db⟩ := smooth_compact_increment sb hk (fun z hz => (off z hz).2.1)
  obtain ⟨c,dc⟩ := smooth_compact_increment sc hk (fun z hz => (off z hz).2.2)
  let L := (c:ℝ)+2*(b:ℝ)+(a:ℝ)
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro t w
  let τ := planeFieldTranslate t
  rw [←τ.norm_map w]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have trans := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp (acts w)
  filter_upwards [Lp.coeFn_sub (T (τ w)) (τ (T w)),acts (τ w),planeFieldTranslate_ae t (T w),
    planeFieldTranslate_ae t w,trans] with z sub atz shift field orig
  change ‖(T (τ w)-τ (T w)) z‖≤L*‖t‖*‖τ w z‖
  change T w (z+t)=planeMetricFlux A B C (z+t) (w (z+t)) at orig
  rw [sub,Pi.sub_apply,atz,shift,field,orig]
  let v := w (z+t)
  let Δ := fun (f : ℂ→ℝ) (x : ℂ) => f x-f (x+t)
  have id : planeMetricFlux A B C z v-planeMetricFlux A B C (z+t) v=
      planeMetricFlux (Δ A) (Δ B) (Δ C) z v := by
    apply Complex.ext <;> simp [planeMetricFlux,Δ] <;> ring
  rw [id]
  apply (planeMetricFlux_norm_le (Δ A) (Δ B) (Δ C) z v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change |C z-C (z+t)|+2*|B z-B (z+t)|+|A z-A (z+t)|≤L*‖t‖
  dsimp only [L]
  linarith [da z t,db z t,dc z t]

/-- Translating an actual compactly supported Lipschitz forcing gives a
linear-in-displacement bound in the ambient L² norm. -/
theorem compact_load_translation_estimate {f : ℂ → ℂ} (compact : HasCompactSupport f)
    {L : ℝ≥0} (lip : LipschitzWith L f) (b : Lp ℂ 2 (volume:Measure ℂ)) (rep : ⇑b =ᵐ[volume] f) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℂ, ‖t‖≤1 → ‖planeFieldTranslate t b-b‖≤M*‖t‖ := by
  obtain ⟨R,hR,cover⟩ := compact.isBounded.subset_ball_lt 0 (0:ℂ)
  let d := diskConstantVector 0 (R+1) 1
  refine ⟨(L:ℝ)*‖d‖,by positivity,?_⟩
  intro t ht
  have normBound : ‖planeFieldTranslate t b-b‖ ≤ ((L:ℝ)*‖t‖)*‖d‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have trans := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp rep
    filter_upwards [Lp.coeFn_sub (planeFieldTranslate t b) b,planeFieldTranslate_ae t b,trans,rep,
      diskConstantVector_ae 0 (R+1) 1] with z sub shift orig atz hd
    change b (z+t)=f (z+t) at orig
    change ‖(planeFieldTranslate t b-b) z‖ ≤ (L:ℝ)*‖t‖*‖d z‖
    rw [sub,Pi.sub_apply,shift,orig,atz,hd]
    by_cases inside : z∈ball (0:ℂ) (R+1)
    · rw [indicator_of_mem inside,norm_one,mul_one]
      simpa [dist_eq_norm] using lip.dist_le_mul (z+t) z
    · have far : R+1≤‖z‖ := by simpa [mem_ball,dist_eq_norm] using inside
      have out : z∉tsupport f := by
        intro mem
        have small := cover mem
        simp [mem_ball,dist_eq_norm] at small
        linarith
      have outt : z+t∉tsupport f := by
        intro mem
        have small := cover mem
        simp [mem_ball,dist_eq_norm] at small
        have tri : ‖z‖≤‖z+t‖+‖t‖ := by simpa using norm_sub_le (z+t) t
        linarith
      rw [image_eq_zero_of_notMem_tsupport outt,image_eq_zero_of_notMem_tsupport out,
        sub_zero,norm_zero,indicator_of_notMem inside,norm_zero,mul_zero]
  calc
    _ ≤ _ := normBound
    _ = _ := by ring
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_conductivity_translation_commutator
#print axioms TwoAxisHelicoid.compact_load_translation_estimate
