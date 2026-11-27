import TwoAxisHelicoid.SpatialMeanDisplacementData
import TwoAxisHelicoid.SpatialThetaQuadrature
import TwoAxisHelicoid.CertifiedHorizontalSegmentMean

namespace TwoAxisHelicoid
open Complex Set Metric ComplexBall

private theorem paired_spatial_observable_bounds (first : Bool) {P N : ComplexBall} {u v : ℂ}
    (hu : P.Contains u) (hv : N.Contains v) :
    let c := (spatialMeanCenter first P.center N.center:ℝ)
    let b := ((P.radius:ℝ)+N.radius)/2
    spatialMeanObservable first false u+spatialMeanObservable first true v∈Icc (c-b) (c+b) := by
  have components {B : ComplexBall} {a : ℂ} (h : B.Contains a) :
      |a.re-(B.center.re:ℝ)|≤B.radius ∧ |a.im-(B.center.im:ℝ)|≤B.radius :=
    ⟨(abs_re_le_norm (a-B.center.val)).trans h,(abs_im_le_norm (a-B.center.val)).trans h⟩
  obtain ⟨pr,pi⟩ := components hu
  obtain ⟨nr,ni⟩ := components hv
  cases first <;> simp [spatialMeanCenter,spatialMeanObservable] <;> constructor <;>
    linarith [(abs_le.mp pr).1,(abs_le.mp pr).2,(abs_le.mp nr).1,(abs_le.mp nr).2,
      (abs_le.mp pi).1,(abs_le.mp pi).2,(abs_le.mp ni).1,(abs_le.mp ni).2]

theorem SpatialMeanDisplacementCell.sound {first : Bool} {e l r R a b : ℚ} (w : SpatialMeanDisplacementCell)
    (ok : w.Valid first e l r R a b) :
    let p := certifiedClosedParameters
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      (∀ x∈Icc (l:ℝ) r, centralBandEdgePoint false e x∉certifiedPeriodPair.lattice) →
      X ⟨r,e⟩ (if first then 0 else 1)-X ⟨l,e⟩ (if first then 0 else 1)∈Icc (a:ℝ) b := by
  intro p X d off
  rcases ok with ⟨lr,cp,cn,lo,hi⟩
  let x := (l+r)/2
  let h := (r-l)/2
  let c : QComplex := ⟨x,e⟩
  let f := thetaA p.t p.a
  obtain ⟨pos,ap⟩ := w.positive.certified_rational_mean rationalQuadrature12_exact rationalQuadrature12_nodes c cp
  obtain ⟨neg,an⟩ := w.negative.certified_rational_mean rationalQuadrature12_exact rationalQuadrature12_nodes ⟨-x,-e⟩ cn
  have cnEq : (QComplex.mk (-x) (-e)).val= -c.val := by apply Complex.ext <;> simp [c,QComplex.val]
  rw [cnEq] at neg an
  have hp : 0≤(h:ℝ) := by exact_mod_cast cp.1
  have hr : (h:ℝ)<R := by exact_mod_cast cp.2.1
  have cont {z : ℂ} (hol : DiffContOnCl ℂ f (ball z (R:ℝ))) :
      ContinuousOn (fun t : ℝ => f (z+((h:ℝ):ℂ)*t)) (Icc (-1:ℝ) 1) :=
    hol.continuousOn_ball.comp (by fun_prop) (fun t ht => mem_closedBall_iff_norm.mpr ((affine_unit_norm_bound hp ht).trans hr.le))
  have xcast : (x:ℝ)=((l:ℝ)+r)/2 := by dsimp [x]; push_cast; rfl
  have hcast : (h:ℝ)=((r:ℝ)-l)/2 := by dsimp [h]; push_cast; rfl
  have eq := actual_horizontal_displacement_by_means first (e:ℝ) (l:ℝ) (r:ℝ) (by exact_mod_cast lr.le) d off
  change (ContinuousOn _ _ → ContinuousOn _ _ → _) at eq
  rw [← xcast,← hcast] at eq
  have mean := eq (cont ap) (cont an)
  have band := paired_spatial_observable_bounds first pos neg
  let P := w.positive.output.toBall slopingFluxAnalyticSetup.config.prec
  let N := w.negative.output.toBall slopingFluxAnalyticSetup.config.prec
  let C := spatialMeanCenter first P.center N.center
  have a' : (a:ℝ)≤((r:ℝ)-l)*((C:ℝ)-((P.radius:ℝ)+N.radius)/2) := by exact_mod_cast lo
  have b' : ((r:ℝ)-l)*((C:ℝ)+((P.radius:ℝ)+N.radius)/2)≤b := by exact_mod_cast hi
  have len : 0≤(r:ℝ)-l := sub_nonneg.mpr (by exact_mod_cast lr.le)
  rw [mean]
  exact ⟨a'.trans (mul_le_mul_of_nonneg_left band.1 len),(mul_le_mul_of_nonneg_left band.2 len).trans b'⟩

theorem CheckedHorizontalDisplacement.ordered {f e l r a b} (c : CheckedHorizontalDisplacement f e l r a b) : l≤r := by
  induction c with
  | cell _ h => exact h.1.le
  | join _ _ left right => exact left.trans right

/-- A partition of horizontal segments gives the endpoint displacement
on the actual immersion, with the computed enclosures added exactly. -/
theorem CheckedHorizontalDisplacement.sound {f e l r a b} (cert : CheckedHorizontalDisplacement f e l r a b) :
    let p := certifiedClosedParameters
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      (∀ x∈Icc (l:ℝ) r, centralBandEdgePoint false e x∉certifiedPeriodPair.lattice) →
      X ⟨r,e⟩ (if f then 0 else 1)-X ⟨l,e⟩ (if f then 0 else 1)∈Icc (a:ℝ) b := by
  induction cert with
  | cell w ok => exact w.sound ok
  | @join l m r a b c d p q ih jh =>
    intro _ X diff off
    have ml : (l:ℝ)≤m := by exact_mod_cast p.ordered
    have mr : (m:ℝ)≤r := by exact_mod_cast q.ordered
    have left := ih diff (fun x hx => off x ⟨hx.1,hx.2.trans mr⟩)
    have right := jh diff (fun x hx => off x ⟨ml.trans hx.1,hx.2⟩)
    simp only [Rat.cast_add,mem_Icc]
    constructor <;> linarith [left.1,left.2,right.1,right.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedHorizontalDisplacement.sound
