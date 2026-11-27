import TwoAxisHelicoid.SmoothTestTranslateL2
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace Topology
open scoped ContDiff RealInnerProductSpace

theorem planeFieldTranslate_zero (u : Lp ℂ 2 (volume:Measure ℂ)) : planeFieldTranslate 0 u=u := by
  apply Lp.ext
  exact (planeFieldTranslate_ae 0 u).mono fun z hz => by simpa only [add_zero] using hz

theorem planeFieldTranslate_add (s t : ℂ) (w : Lp ℂ 2 (volume:Measure ℂ)) :
    planeFieldTranslate (s+t) w=planeFieldTranslate t (planeFieldTranslate s w) := by
  apply Lp.ext
  have sh := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp (planeFieldTranslate_ae s w)
  filter_upwards [planeFieldTranslate_ae (s+t) w,planeFieldTranslate_ae t (planeFieldTranslate s w),sh] with z e h k
  change planeFieldTranslate s w (z+t)=w (z+t+s) at k
  exact e.trans ((congrArg (fun x => w x) (show z+(s+t)=z+t+s by abel)).trans (h.trans k).symm)

def HasPlaneL2WeakDerivative (u q : Lp ℂ 2 (volume:Measure ℂ)) (d : ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ z, ⟪q z,φ z⟫_ℝ) = -(∫ z, ⟪u z,fderiv ℝ φ z d⟫_ℝ)

/-- Differentiating the translation orbit produces the distributional derivative
itself. Its own orbit remains smooth, so the argument can be iterated. -/
theorem smooth_orbit_weak_derivative (u : Lp ℂ 2 (volume:Measure ℂ))
    (smooth : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u)) (d : ℂ) :
    ∃ q : Lp ℂ 2 (volume:Measure ℂ), HasPlaneL2WeakDerivative u q d ∧
      ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t q) := by
  let F := fun t : ℂ => planeFieldTranslate t u
  let q := fderiv ℝ F 0 d
  have df : Differentiable ℝ F := smooth.differentiable (by simp)
  have translate (t x : ℂ) : F (x+t)=planeFieldTranslate t (F x) := planeFieldTranslate_add x t u
  have identity (t : ℂ) : planeFieldTranslate t q=fderiv ℝ F t d := by
    have id : (fun x => F (x+t))=(planeFieldTranslate t).toContinuousLinearMap ∘ F := funext (translate t)
    have eq := congrArg (fun g : ℂ → Lp ℂ 2 (volume:Measure ℂ) => fderiv ℝ g 0 d) id
    rw [fderiv_comp_add_right,zero_add,fderiv_comp 0 (planeFieldTranslate t).toContinuousLinearMap.differentiableAt (df 0),
      ContinuousLinearMap.fderiv] at eq
    exact eq.symm
  refine ⟨q,?_,?_⟩
  · intro φ s h
    let m := s.continuous.memLp_of_hasCompactSupport (μ:=volume) (p:=2) h
    let test := m.toLp φ
    let deriv := fun z => fderiv ℝ φ z (-d)
    have cd : Continuous deriv := (s.continuous_fderiv (by simp)).clm_apply continuous_const
    let n := cd.memLp_of_hasCompactSupport (μ:=volume) (p:=2) (h.fderiv_apply ℝ (-d))
    let v := n.toLp deriv
    have ltest := compact_test_translate_quotient_tendsto s h test m.coeFn_toLp (-d) v n.coeFn_toLp
    have line : HasDerivAt (fun a : ℝ => a • d) d 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const d
    have qline : HasDerivAt (fun a : ℝ => F (a • d)) q 0 := by
      change HasDerivAt (F ∘ (fun a : ℝ => a • d)) (fderiv ℝ F 0 d) 0
      exact (df 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 line (by simp)
    have limq : Tendsto (fun a : ℝ => a⁻¹ • (planeFieldTranslate (a • d) u-u)) (𝓝[>] 0) (𝓝 q) := by
      have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp qline).2
      change Tendsto (fun a : ℝ => (a-0)⁻¹ • (F (a • d)-F ((0:ℝ) • d))) (𝓝[>] 0) (𝓝 q) at hlim
      simpa only [sub_zero,zero_smul,F,planeFieldTranslate_zero] using hlim
    have dual (t : ℂ) : ⟪planeFieldTranslate t u,test⟫_ℝ=⟪u,planeFieldTranslate (-t) test⟫_ℝ := by
      have e := (planeFieldTranslate t).inner_map_map u (planeFieldTranslate (-t) test)
      rwa [planeFieldTranslate_cancel] at e
    have h1 := (((Continuous.inner (𝕜:=ℝ) continuous_id (continuous_const (y:=test))).continuousAt (x:=q)).tendsto.comp limq)
    have h2 := (((Continuous.inner (𝕜:=ℝ) (continuous_const (y:=u)) continuous_id).continuousAt (x:=v)).tendsto.comp ltest)
    have per (a : ℝ) : ⟪a⁻¹ • (planeFieldTranslate (a • d) u-u),test⟫_ℝ=
        ⟪u,a⁻¹ • (planeFieldTranslate (a • (-d)) test-test)⟫_ℝ := by
      simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right,smul_neg,dual]
    have eq : ⟪q,test⟫_ℝ=⟪u,v⟫_ℝ := tendsto_nhds_unique_of_eventuallyEq h1 h2 (Eventually.of_forall per)
    rw [L2.inner_def,L2.inner_def] at eq
    calc
      _ = (∫ z, ⟪q z,test z⟫_ℝ) := integral_congr_ae (m.coeFn_toLp.symm.mono fun z e => congrArg (fun x : ℂ => ⟪q z,x⟫_ℝ) e)
      _ = (∫ z, ⟪u z,v z⟫_ℝ) := eq
      _ = (∫ z, -⟪u z,fderiv ℝ φ z d⟫_ℝ) := by
        apply integral_congr_ae
        filter_upwards [n.coeFn_toLp] with z e
        rw [e]
        simp only [deriv,map_neg,inner_neg_right]
      _ = _ := integral_neg _
  · rw [show (fun t => planeFieldTranslate t q)=(fun t => fderiv ℝ F t d) from funext identity]
    exact (smooth.fderiv_right (by simp)).clm_apply contDiff_const

/-- Iterated distributional derivatives along a prescribed finite list of
real directions are represented by square-integrable fields. -/
def HasIteratedPlaneL2Derivatives (u : Lp ℂ 2 (volume:Measure ℂ)) : List ℂ → Prop
  | [] => True
  | d::ds => ∃ q, HasPlaneL2WeakDerivative u q d ∧ HasIteratedPlaneL2Derivatives q ds

theorem smooth_orbit_has_all_weak_derivatives (u : Lp ℂ 2 (volume:Measure ℂ))
    (s : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u)) (ds : List ℂ) :
    HasIteratedPlaneL2Derivatives u ds := by
  induction ds generalizing u with
  | nil => exact trivial
  | cons d ds ih =>
    obtain ⟨q,der,sq⟩ := smooth_orbit_weak_derivative u s d
    exact ⟨q,der,ih q sq⟩
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_orbit_has_all_weak_derivatives
