import TwoAxisHelicoid.TraceDataSlopingSpatialMesh
import TwoAxisHelicoid.SlopingDisplacementBounds

namespace TwoAxisHelicoid
open Complex Set

noncomputable def slopingLongitudinalRate (t a s : ℝ) : ℝ :=
  -(((1-I*t)/2)*(thetaA t a (originalPeriodPath t s)+thetaA t a (originalPeriodPath t (-s)))).re/2

theorem sloping_longitudinal_spatial_derivative {t a : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    HasDerivAt (fun u => X (originalPeriodPath t u) 0) (slopingLongitudinalRate t a s) s := by
  have off := rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht ⟨by linarith [hs.1],hs.2⟩)
  have deriv := (actual_coordinate_primitive_component ht d off 0).comp_hasDerivAt s (originalPeriodPath_hasDerivAt t s)
  let v : ℂ := (1-I*t)/2
  let b := thetaA t a (originalPeriodPath t s)
  let c := thetaA t a (originalPeriodPath t (-s))
  change HasDerivAt _ (v*(-(1:ℂ)/2*(thetaA t a (-originalPeriodPath t s)+thetaA t a (originalPeriodPath t s)))).re s at deriv
  rw [thetaA_originalPath_neg] at deriv
  change HasDerivAt _ (v*(-1/2*(c+b))).re s at deriv
  change HasDerivAt _ (-(v*(b+c)).re/2) s
  rwa [show v*(-1/2*(c+b))= -(v*(b+c))/2 by ring,div_ofNat_re,neg_re] at deriv

namespace TraceData

private theorem sum_product_interpret (w : SlopingFluxCell) (prec : Nat) (v : DyadicBall) :
    (w.sumProduct prec v).interpret =
      (v.interpret.toBall prec).mul ((w.plusTheta.output.interpret.toBall prec).add (w.minusTheta.output.interpret.toBall prec)) := by
  simp only [SlopingFluxCell.sumProduct,ComplexBall.interpret,QComplex.interpret,
    DyadicBall.toBall,DyadicBall.interpret,QComplex.mul,QComplex.absUpper,rat_abs_eq,
    ComplexBall.add,QComplex.add,TwoAxisHelicoid.DyadicBall.toBall,TwoAxisHelicoid.ComplexBall.mul,TwoAxisHelicoid.ComplexBall.add,
    TwoAxisHelicoid.QComplex.mul,TwoAxisHelicoid.QComplex.absUpper,TwoAxisHelicoid.QComplex.add]
  rfl

theorem SlopingFluxCell.longitudinal_rate_bounds (w : SlopingFluxCell) {t a s : ℝ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper)
    {l r lo hi : ℚ} (hs : s∈Icc (l:ℝ) r)
    (check : w.check slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output l r=true)
    (bound : w.longitudinalBounds slopingFluxDataSetup.config.prec slopingFluxWeight.output lo hi) :
    slopingLongitudinalRate t a s ∈ Icc (lo:ℝ) hi := by
  obtain ⟨ht',hq,ha',hc,hv⟩ := sloping_flux_root_parameter_enclosures ht ha
  obtain ⟨hp,hm⟩ := w.kernel_enclosures slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid slopingFluxParams
    slopingFluxWeight.output ht' hq ha' hc hv hs.1 hs.2 check
  let B := w.sumProduct slopingFluxDataSetup.config.prec slopingFluxWeight.output
  let z := ((1-I*t)/2)*(thetaA t a (originalPeriodPath t s)+thetaA t a (originalPeriodPath t (-s)))
  have mem : B.interpret.Contains z := by
    rw [show B.interpret=_ from sum_product_interpret ..]
    exact TwoAxisHelicoid.ComplexBall.mul_contains hv (TwoAxisHelicoid.ComplexBall.add_contains hp hm)
  have proj := (Complex.abs_re_le_norm (z-B.interpret.center.val)).trans mem
  change |z.re-(B.center.re:ℝ)|≤(B.radius:ℝ) at proj
  obtain ⟨left,right⟩ := abs_le.mp proj
  have bd : 2*(lo:ℝ)≤ -((B.center.re:ℝ)+B.radius) ∧ -((B.center.re:ℝ)-B.radius)≤2*(hi:ℝ) := by
    change 2*lo ≤ -(B.center.re+B.radius) ∧ -(B.center.re-B.radius) ≤ 2*hi at bound
    exact_mod_cast bound
  change (lo:ℝ)≤ -z.re/2 ∧ -z.re/2≤(hi:ℝ)
  constructor <;> linarith [bd.1,bd.2]

structure SlopingScalarBounds.Realizes (q : SlopingScalarBounds) (f rate : ℝ → ℝ) (l r : ℝ) : Prop where
  ordered : l≤r
  rates : ∀ x∈Icc l r, rate x∈Icc (q.rateLo:ℝ) q.rateHi
  total : f r-f l∈Icc (q.totalLo:ℝ) q.totalHi
  part : ∀ x y : ℝ, l≤x → x≤y → y≤r → f y-f x∈Icc (q.partLo:ℝ) q.partHi

private theorem scalar_cell_increments {f rate : ℝ → ℝ} {l r lo hi : ℝ}
    (df : ∀ x∈Icc l r, HasDerivAt f (rate x) x)
    (bd : ∀ x∈Icc l r, rate x∈Icc lo hi) {x y : ℝ} (lx : l≤x) (xy : x≤y) (yr : y≤r) :
    lo*(y-x)≤f y-f x ∧ f y-f x≤hi*(y-x) := by
  rcases xy.eq_or_lt with h|h
  · simp [h]
  · have sub := Icc_subset_Icc lx yr
    obtain ⟨s,hs,eq⟩ := exists_hasDerivAt_eq_slope f rate h
      (fun v hv => (df v (sub hv)).continuousAt.continuousWithinAt) (fun v hv => df v (sub (Ioo_subset_Icc_self hv)))
    have both := bd s (sub (Ioo_subset_Icc_self hs))
    rw [eq] at both
    exact ⟨(le_div_iff₀ (sub_pos.mpr h)).mp both.1,(div_le_iff₀ (sub_pos.mpr h)).mp both.2⟩

private theorem scalar_envelope_join {f d : ℝ → ℝ} {l m r : ℝ} {a b : SlopingScalarBounds}
    (A : a.Realizes f d l m) (B : b.Realizes f d m r) : (a.join b).Realizes f d l r := by
  have za := A.part m m A.ordered le_rfl le_rfl
  have zb := B.part m m le_rfl le_rfl B.ordered
  simp only [sub_self,mem_Icc] at za zb
  refine ⟨A.ordered.trans B.ordered,?_,?_,?_⟩
  · intro x hx
    simp only [SlopingScalarBounds.join,Rat.cast_min,Rat.cast_max,mem_Icc]
    rcases le_total x m with h|h
    · have v := A.rates x ⟨hx.1,h⟩
      exact ⟨(min_le_left _ _).trans v.1,v.2.trans (le_max_left _ _)⟩
    · have v := B.rates x ⟨h,hx.2⟩
      exact ⟨(min_le_right _ _).trans v.1,v.2.trans (le_max_right _ _)⟩
  · simp only [SlopingScalarBounds.join,Rat.cast_add,mem_Icc]
    constructor <;> linarith [A.total.1,A.total.2,B.total.1,B.total.2]
  · intro x y lx xy yr
    simp only [SlopingScalarBounds.join,Rat.cast_add,mem_Icc]
    rcases le_total y m with h|h
    · have v := A.part x y lx xy h
      constructor <;> linarith [v.1,v.2,zb.1,zb.2]
    · rcases le_total m x with k|k
      · have v := B.part x y k xy yr
        constructor <;> linarith [v.1,v.2,za.1,za.2]
      · have left := A.part x m lx k le_rfl
        have right := B.part m y le_rfl h yr
        constructor <;> linarith [left.1,left.2,right.1,right.2]

theorem CheckedSlopingScalar.sound {first : Bool} {t a : ℝ}
    (ht : t∈Icc (rootTLower:ℝ) rootTUpper) (ha : a∈Icc (rootALower:ℝ) rootAUpper) {f : ℝ → ℝ}
    (df : ∀ s∈Icc (0:ℝ) 1, HasDerivAt f ((if first then slopingLongitudinalRate else slopingTransverseRate) t a s) s)
    {l r : ℚ} {q : SlopingScalarBounds}
    (C : CheckedSlopingScalar first slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output l r q) :
    q.Realizes f ((if first then slopingLongitudinalRate else slopingTransverseRate) t a) l r := by
  induction C with
  | cell w l r lo hi domain data rate =>
    have d0 : (0:ℝ)≤l := by exact_mod_cast domain.1
    have lr : (l:ℝ)≤r := by exact_mod_cast domain.2.1.le
    have d1 : (r:ℝ)≤1 := by exact_mod_cast domain.2.2
    have bd (s : ℝ) (hs : s∈Icc (l:ℝ) r) :
        (if first then slopingLongitudinalRate else slopingTransverseRate) t a s∈Icc (lo:ℝ) hi := by
      cases first
      · exact w.transverse_rate_bounds ht ha hs data rate
      · exact w.longitudinal_rate_bounds ht ha hs data rate
    have step := fun {x y : ℝ} (lx : (l:ℝ)≤x) (xy : x≤y) (yr : y≤(r:ℝ)) =>
      scalar_cell_increments (fun s hs => df s (Icc_subset_Icc d0 d1 hs)) bd lx xy yr
    refine ⟨lr,bd,?_,?_⟩
    · simpa only [SlopingScalarBounds.cell,Rat.cast_mul,Rat.cast_sub,mem_Icc] using step le_rfl lr le_rfl
    · intro x y lx xy yr
      have e := step lx xy yr
      simp only [SlopingScalarBounds.cell,Rat.cast_mul,Rat.cast_min,Rat.cast_max,Rat.cast_zero,Rat.cast_sub,mem_Icc]
      have w : y-x≤(r:ℝ)-l := by linarith
      exact ⟨(mul_le_mul_of_nonpos_left w (min_le_right _ _)).trans
          ((mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr xy)).trans e.1),
        e.2.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr xy)).trans
          (mul_le_mul_of_nonneg_left w (le_max_right _ _)))⟩
  | join _ _ A B => exact scalar_envelope_join A B
  | relabel _ eq ih => exact eq ▸ ih

end TraceData
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TraceData.CheckedSlopingScalar.sound
