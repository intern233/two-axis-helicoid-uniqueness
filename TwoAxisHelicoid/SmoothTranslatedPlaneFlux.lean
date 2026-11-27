import TwoAxisHelicoid.BoundedCoefficientMultiplier
import TwoAxisHelicoid.WholePlaneWeakCorrector

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter
open scoped ContDiff BoundedContinuousFunction

/-- The translated physical conductivity, as a smoothly varying bounded
operator on the full-plane vector field space. -/
theorem exists_smooth_translated_plane_flux {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ T : ℂ → Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ),
      ContDiff ℝ ∞ T ∧ ∀ t w, ⇑(T t w) =ᵐ[volume] (fun z => planeMetricFlux A B C (z+t) (w z)) := by
  let E := Lp ℂ 2 (volume:Measure ℂ)
  let a := fun z => A z-1
  let c := fun z => C z-1
  have comp {f : ℂ → ℝ} (eq : ∀ z∉K, f z=0) : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hk
    exact fun z hz => by_contra fun out => hz (eq z out)
  have ac : HasCompactSupport a := comp (fun z hz => sub_eq_zero.mpr (off z hz).1)
  have bc : HasCompactSupport B := comp (fun z hz => (off z hz).2.1)
  have cc : HasCompactSupport c := comp (fun z hz => sub_eq_zero.mpr (off z hz).2.2)
  have as' : ContDiff ℝ ∞ a := sa.sub contDiff_const
  have cs : ContDiff ℝ ∞ c := sc.sub contDiff_const
  let at' := compactCoefficientTranslate a as'.continuous ac
  let bt := compactCoefficientTranslate B sb.continuous bc
  let ct := compactCoefficientTranslate c cs.continuous cc
  obtain ⟨J,hJ⟩ := exists_bounded_coefficient_multiplier
  let X := Complex.ofRealCLM.comp Complex.reCLM
  let Y : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℂ)-X
  let Z : ℂ →L[ℝ] ℂ := -(Complex.ofRealCLM.comp Complex.imCLM)-I • X
  let px := X.compLpL 2 (volume:Measure ℂ)
  let py := Y.compLpL 2 (volume:Measure ℂ)
  let pz := Z.compLpL 2 (volume:Measure ℂ)
  let T := fun t => (ContinuousLinearMap.id ℝ E) + (J (ct t)).comp px +
    (J (at' t)).comp py + (J (bt t)).comp pz
  have s1 := (J.contDiff.comp (smooth_compactCoefficientTranslate cs cc)).clm_comp (contDiff_const (c:=px))
  have s2 := (J.contDiff.comp (smooth_compactCoefficientTranslate as' ac)).clm_comp (contDiff_const (c:=py))
  have s3 := (J.contDiff.comp (smooth_compactCoefficientTranslate sb bc)).clm_comp (contDiff_const (c:=pz))
  refine ⟨T,((contDiff_const.add s1).add s2).add s3,?_⟩
  intro t w
  let x := J (ct t) (px w)
  let y := J (at' t) (py w)
  let z := J (bt t) (pz w)
  change ⇑(((w+x)+y)+z) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add ((w+x)+y) z,Lp.coeFn_add (w+x) y,Lp.coeFn_add w x,
    hJ (ct t) (px w),hJ (at' t) (py w),hJ (bt t) (pz w),
    X.coeFn_compLpL w,Y.coeFn_compLpL w,Z.coeFn_compLpL w]
    with v total middle first xx yy zz d1 d2 d3
  rw [total,Pi.add_apply,middle,Pi.add_apply,first,Pi.add_apply,xx,yy,zz,d1,d2,d3]
  change w v+c (v+t) • X (w v)+a (v+t) • Y (w v)+B (v+t) • Z (w v)=_
  apply Complex.ext <;> simp [planeMetricFlux,a,c,X,Y,Z,Complex.mul_re,Complex.mul_im] <;> ring
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_smooth_translated_plane_flux
