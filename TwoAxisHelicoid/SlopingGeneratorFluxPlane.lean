import TwoAxisHelicoid.OriginalCycleHorizontalFlux
import TwoAxisHelicoid.OriginalHeightPeriod
import TwoAxisHelicoid.WeierstrassVerticalDomain
import TwoAxisHelicoid.TorusSpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace
open scoped ComplexConjugate Topology

/-- The reflected generator is measured in the same marking as the
original sloping generator. -/
noncomputable def conjugateSlopingFluxArc {t : ℝ} (ht : 0<t) :
    ComplexPeriodArc ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ where
  left := -1
  right := 1
  ordered := by norm_num
  curve := fun s => conj (originalPeriodPath t s)
  velocity := fun _ => (1+I*t)/2
  stays := by
    intro s hs bad
    exact rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs) (by
      simpa only [Complex.conj_conj] using rhombic_conj_mem ht bad)
  continuous_curve := by unfold originalPeriodPath; fun_prop
  continuous_velocity := continuousOn_const
  derivative := by
    intro s _
    have d := conjCLE.hasFDerivAt.comp_hasDerivAt s (originalPeriodPath_hasDerivAt t s)
    change HasDerivAt (fun r => conj (originalPeriodPath t r)) _ s
    convert d using 1
    · funext r
      exact (conjCLE_apply _).symm
    · change (1+I*(t:ℂ))/2=conj ((1-I*(t:ℂ))/2)
      simp [map_ofNat]

private theorem quotient_arc_spatial_flux {L : PeriodPair} (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
    (closed : periodTorusProjection L (A.curve A.left)=periodTorusProjection L (A.curve A.right))
    (w : Fin 3 → ℂ) (values : ∀ j, A.integral (fun z => torusImmersionForms L X z j)=w j) :
    ∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j γ (w j).im := by
  have eq : A.start=A.finish := Subtype.ext closed
  refine ⟨A.start,A.projected.cast rfl eq,fun j => (torus_spatial_conormal_integral_iff L X reg _ j _).mpr ⟨w j,?_,rfl⟩⟩
  have h : TorusPathIntegral L (fun z => torusImmersionForms L X z j) A.projected
      (A.integral (fun z => torusImmersionForms L X z j)) := .arc A.projected A (fun _ => rfl)
  rw [values] at h
  exact h.cast rfl eq


theorem sloping_generator_parameter_arcs {t a c : ℝ} (ht : 0<t) :
    let L := rhombicPeriodPair t ht
    let measured := fun w : Fin 3 → ℂ => ∃ A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ,
      periodTorusProjection L (A.curve A.left)=periodTorusProjection L (A.curve A.right) ∧
      ∀ j, A.integral (fun z => coordinateData t a c ht z j)=w j
    measured (originalCoordinatePeriod t a c ht) ∧ measured (conjugateCoordinatePeriod t a c ht) := by
  let L := rhombicPeriodPair t ht
  constructor
  · let A := originalSlopingFluxArc ht
    refine ⟨A,?_,fun j => ?_⟩
    · apply (periodTorusProjection_eq_iff L _ _).mpr
      apply PeriodPair.mem_lattice.mpr
      refine ⟨1,-1,?_⟩
      simp [A,originalSlopingFluxArc,originalPeriodPath,L,rhombicPeriodPair]
      ring
    · unfold ComplexPeriodArc.integral originalCoordinatePeriod
      rw [← intervalIntegral.integral_const_mul]
      rfl
  · let A := conjugateSlopingFluxArc ht
    refine ⟨A,?_,fun j => ?_⟩
    · apply (periodTorusProjection_eq_iff L _ _).mpr
      apply PeriodPair.mem_lattice.mpr
      refine ⟨0,1,?_⟩
      simp [A,conjugateSlopingFluxArc,originalPeriodPath,L,rhombicPeriodPair,map_ofNat]
      ring
    · unfold ComplexPeriodArc.integral conjugateCoordinatePeriod
      rw [← intervalIntegral.integral_const_mul]
      rfl

theorem sloping_generator_spatial_fluxes {t a c : ℝ} (ht : 0<t)
    (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (reg : ∀ z∉(rhombicPeriodPair t ht).lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback _ X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback _ X) z)
    (hd : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback _ X) t a c ht) :
    let L := rhombicPeriodPair t ht
    (∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j γ (originalCoordinatePeriod t a c ht j).im) ∧
    (∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j γ (conjugateCoordinatePeriod t a c ht j).im) := by
  let L := rhombicPeriodPair t ht
  have form (z : ℂ) (hz : z∉L.lattice) : torusImmersionForms L X z=coordinateData t a c ht z := by
    have same := ((immersionComplexCoefficient_hasFDerivAt (hd z hz).differentiableAt).unique (hd z hz))
    change immersionComplexCoefficient (puncturedTorusPullback _ X) z=coordinateData t a c ht z
    funext j
    apply Complex.ext
    · simpa using congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D 1 j) same
    · simpa using congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D I j) same

  have measure (w : Fin 3 → ℂ) (A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
      (cl : periodTorusProjection L (A.curve A.left)=periodTorusProjection L (A.curve A.right))
      (val : ∀ j, A.integral (fun z => coordinateData t a c ht z j)=w j) :
      ∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j γ (w j).im := by
    apply quotient_arc_spatial_flux X reg A cl
    intro j
    rw [← val]
    apply intervalIntegral.integral_congr
    intro s hs
    change A.velocity s*torusImmersionForms L X (A.curve s) j=_
    rw [form _ (A.stays (by simpa only [uIcc_of_le A.ordered] using hs))]
  obtain ⟨⟨A,hA,mA⟩,B,hB,mB⟩ := sloping_generator_parameter_arcs (a := a) (c := c) ht
  exact ⟨measure _ A hA mA,measure _ B hB mB⟩

/-- For a closed height period, the vertical flux on each sloping
generator is exactly minus pi times the scale divided by the height. -/
theorem original_sloping_vertical_flux {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (closed : thetaG t a=0) :
    (originalCoordinatePeriod t a c ht 2).im= -(Real.pi*c/t) := by
  rw [originalCoordinatePeriod_height ht]
  simp only [Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.one_im,thetaEtaExpression_real,rhombic_weierstrassP_real]
  rw [(thetaG_zero_iff_wp_level ht ha).mp closed]
  ring

/-- The two fluxes are linearly independent even after discarding their
second coordinate. Their span is an ambient-plane invariant. -/
theorem sloping_generator_flux_minor_ne_zero {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    (closed : thetaG t a=0) (horizontal : (originalSlopingPeriod t a).im≠0) :
    let v := fun j => (originalCoordinatePeriod t a c ht j).im
    let w := fun j => (conjugateCoordinatePeriod t a c ht j).im
    v 0*w 2-w 0*v 2≠0 := by
  dsimp only
  rw [(conjugateCoordinatePeriod_horizontal ht).1,conjugateCoordinatePeriod_height ht,Complex.conj_im,Complex.neg_im,
    Complex.conj_im,neg_neg,original_sloping_vertical_flux ht ha closed,(originalCoordinatePeriod_horizontal ht).1]
  simp only [Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,neg_zero,
    zero_mul,add_zero]
  have n := div_ne_zero (mul_ne_zero Real.pi_ne_zero hc) ht.ne'
  intro bad
  exact (mul_ne_zero (mul_ne_zero hc horizontal) n) (by linarith)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_generator_spatial_fluxes
#print axioms TwoAxisHelicoid.sloping_generator_flux_minor_ne_zero
