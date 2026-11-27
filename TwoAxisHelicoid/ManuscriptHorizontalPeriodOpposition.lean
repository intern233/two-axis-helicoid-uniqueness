import TwoAxisHelicoid.PeriodicCoefficientComplexPrimitive
import TwoAxisHelicoid.FullTorusHorizontalPeriods
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology

/-- The two horizontal differentials g dh and dh/g, continued through
the finite Gauss divisor as in Section 6. -/
noncomputable def manuscriptOmegaPlus (t a c : ℝ) (z : ℂ) : ℂ := c*thetaA t a z
noncomputable def manuscriptOmegaMinus (t a c : ℝ) (z : ℂ) : ℂ := -manuscriptOmegaPlus t a c (-z)

theorem manuscript_omega_gauss_height {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) {z : ℂ}
    (hz : z∉(rhombicPeriodPair t ht).lattice) (hm : z-a∉(rhombicPeriodPair t ht).lattice)
    (hp : z+a∉(rhombicPeriodPair t ht).lattice) :
    manuscriptOmegaPlus t a c z=thetaGauss t a 1 z*(coordinateData t a c ht z 2) ∧
    manuscriptOmegaMinus t a c z=(thetaGauss t a 1 z)⁻¹*(coordinateData t a c ht z 2) := by
  let L := rhombicPeriodPair t ht
  have hA := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a<2)
  have plus := thetaGauss_height_sigma_of_pos ht ht c hA hz hp
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht z hA hz] at plus
  have hnz : -z∉L.lattice := by simpa using hz
  have hnp : -z+a∉L.lattice := by simpa only [show -z+(a:ℂ)= -(z-a) by ring,neg_mem_iff] using hm
  have minus := thetaGauss_height_sigma_of_pos ht ht c hA hnz hnp
  have gneg : thetaGauss t a 1 (-z)= -(thetaGauss t a 1 z)⁻¹ := by
    apply mul_right_cancel₀ (thetaGauss_ne_zero ht a 1 hm hp)
    rw [thetaGauss_neg_product ht a 1 hm hp]
    simp [thetaGauss_ne_zero ht a 1 hm hp]
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht (-z) hA hnz,gneg,L.weierstrassP_neg] at minus
  constructor
  · exact plus.symm
  · change -((c:ℂ)*thetaA t a (-z)) = (thetaGauss t a 1 z)⁻¹*(I*c*(L.weierstrassP z-L.weierstrassP a))
    linear_combination -minus.symm

private theorem arc_complex_primitive {L : PeriodPair} (p : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
    {f F : ℂ → ℂ} (hf : ContinuousOn f (L.lattice : Set ℂ)ᶜ)
    (hF : ∀ z∉L.lattice, HasDerivAt F (f z) z) :
    p.integral f=F (p.curve p.right)-F (p.curve p.left) := by
  have integrable : IntervalIntegrable (fun s => p.velocity s*f (p.curve s)) volume p.left p.right :=
    (p.continuous_velocity.mul (hf.comp p.continuous_curve p.stays)).intervalIntegrable_of_Icc p.ordered
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le p.ordered
    ((show ContinuousOn F (L.lattice : Set ℂ)ᶜ from fun z hz =>
      (hF z hz).continuousAt.continuousWithinAt).comp p.continuous_curve p.stays)
  · intro s hs
    exact (hF _ (p.stays (Ioo_subset_Icc_self hs))).scomp s (p.derivative s hs)
  · exact integrable

private theorem transfer_arc_integrals {L : PeriodPair} {f g : ℂ → ℂ} (V : PeriodTorus L → ℂ)
    (arcs : ∀ p : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ,
      p.integral g=V p.finish.1-V p.start.1-p.integral f)
    {q r : PuncturedPeriodTorus L} {γ : Path q r} {v : ℂ} (h : TorusPathIntegral L f γ v) :
    TorusPathIntegral L g γ (V r.1-V q.1-v) := by
  induction h with
  | refl q => simpa using (TorusPathIntegral.refl (L:=L) (f:=g) q)
  | arc γ a rep =>
    have start := rep 0
    have finish := rep 1
    simp only [γ.source,γ.target,ComplexPeriodArc.time,Set.Icc.coe_zero,Set.Icc.coe_one,
      AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] at start finish
    rw [start,finish]
    change TorusPathIntegral L g γ (V a.finish.1-V a.start.1-a.integral f)
    rw [← arcs a]
    exact .arc γ a rep
  | trans _ _ ih₁ ih₂ =>
    convert TorusPathIntegral.trans ih₁ ih₂ using 1
    ring

/-- A holomorphic coefficient periodic on a once-punctured rhombic torus
has a primitive upstairs. Addition of a fixed lattice period changes
the primitive by a constant, independently of the point upstairs. -/
private theorem translated_primitive_increment {L : PeriodPair} {f F : ℂ → ℂ}
    (hF : ∀ z∉L.lattice, HasDerivAt F (f z) z)
    (per : ∀ z ω, ω∈L.lattice → f (z+ω)=f z) {ω : ℂ} (hω : ω∈L.lattice) :
    ∃ b : ℂ, ∀ z∉L.lattice, F (z+ω)=F z+b := by
  have off {z : ℂ} (hz : z∉L.lattice) : z+ω∉L.lattice := by
    intro h
    exact hz (by simpa using L.lattice.sub_mem h hω)
  have shifted (z : ℂ) (hz : z∉L.lattice) : HasDerivAt (fun w => F (w+ω)) (f z) z := by
    simpa only [per z ω hω] using (hF _ (off hz)).comp_add_const z ω
  have conn : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
    refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact countable_of_Lindelof_of_discrete (X := L.lattice)
  obtain ⟨b,hb⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_deriv_eq conn
    (fun z hz => (shifted z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (shifted z hz).deriv.trans (hF z hz).deriv.symm)
  exact ⟨b,fun z hz => hb hz⟩

private theorem piecewise_complex_primitive {L : PeriodPair} {x y : ℂ}
    (p : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y)
    {f F : ℂ → ℂ} (hf : ContinuousOn f (L.lattice : Set ℂ)ᶜ)
    (hF : ∀ z∉L.lattice, HasDerivAt F (f z) z) : p.integral f=F y-F x := by
  induction p with
  | refl => simp [PiecewiseComplexPath.integral]
  | arc a => exact arc_complex_primitive a hf hF
  | trans p q hp hq => simp only [PiecewiseComplexPath.integral,hp,hq]; ring

/-- Literal integral equality on every piecewise smooth lift of a closed
curve. A nonzero endpoint lattice displacement is allowed. -/
theorem manuscript_horizontal_integral_negative {t : ℝ} (ht : 0<t) (a c : ℝ) {x y : ℂ}
    (γ : PiecewiseComplexPath ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ x y)
    (closed : periodTorusProjection (rhombicPeriodPair t ht) x=periodTorusProjection (rhombicPeriodPair t ht) y) :
    γ.integral (manuscriptOmegaMinus t a c) = -γ.integral (manuscriptOmegaPlus t a c) := by
  let L := rhombicPeriodPair t ht
  let f := manuscriptOmegaPlus t a c
  have analytic (z : ℂ) (hz : z∉L.lattice) : AnalyticAt ℂ f z :=
    analyticAt_const.mul (thetaA_analyticAt_off_lattice ht a hz)
  have per (z ω : ℂ) (hω : ω∈L.lattice) : f (z+ω)=f z :=
    congrArg ((c:ℂ)*·) (thetaA_add_lattice ht a z ⟨ω,hω⟩)
  obtain ⟨F,dF⟩ := periodic_coefficient_unrestricted_complex_primitive ht analytic per
  have dg (z : ℂ) (hz : z∉L.lattice) : HasDerivAt (fun w => F (-w)) (manuscriptOmegaMinus t a c z) z := by
    have off : -z∉L.lattice := by simpa using hz
    simpa only [manuscriptOmegaMinus,Function.comp_def,mul_neg,mul_one] using
      (dF (-z) off).comp z (hasDerivAt_id z).neg
  have cg : ContinuousOn (manuscriptOmegaMinus t a c) (L.lattice : Set ℂ)ᶜ := by
    intro z hz
    have off : -z∉L.lattice := by simpa using hz
    exact (((analytic (-z) off).continuousAt.comp continuous_neg.continuousAt).neg).continuousWithinAt
  obtain ⟨hx,hy,_,_⟩ := γ.projected_hasIntegral f
  obtain ⟨k,hk⟩ := translated_primitive_increment dF per ((periodTorusProjection_eq_iff L x y).mp closed)
  have xy := hk x hx
  have yx := hk (-y) (by simpa using hy)
  rw [show x+(y-x)=y by ring] at xy
  rw [show -y+(y-x)= -x by ring] at yx
  rw [piecewise_complex_primitive γ cg dg,
      piecewise_complex_primitive γ (fun z hz => (analytic z hz).continuousAt.continuousWithinAt) dF]
  linear_combination -yx + xy

/-- On every closed path in the punctured torus the possible integral
values of dh/g are exactly the negatives of those of g dh. This
includes arbitrary subdivisions and independent lattice lifts. Neither
horizontal nor vertical period closure is required. -/
theorem manuscript_horizontal_periods_opposite {t : ℝ} (ht : 0<t) (a c : ℝ)
    {q : PuncturedPeriodTorus (rhombicPeriodPair t ht)} (γ : Path q q) (v : ℂ) :
    TorusPathIntegral (rhombicPeriodPair t ht) (manuscriptOmegaPlus t a c) γ v ↔
      TorusPathIntegral (rhombicPeriodPair t ht) (manuscriptOmegaMinus t a c) γ (-v) := by
  classical
  let L := rhombicPeriodPair t ht
  let f := manuscriptOmegaPlus t a c
  let g := manuscriptOmegaMinus t a c
  have analytic (z : ℂ) (hz : z∉L.lattice) : AnalyticAt ℂ f z :=
    analyticAt_const.mul (thetaA_analyticAt_off_lattice ht a hz)
  have per (z ω : ℂ) (hω : ω∈L.lattice) : f (z+ω)=f z :=
    congrArg ((c:ℂ)*·) (thetaA_add_lattice ht a z ⟨ω,hω⟩)
  obtain ⟨F,dF⟩ := periodic_coefficient_unrestricted_complex_primitive ht analytic per
  have contf : ContinuousOn f (L.lattice : Set ℂ)ᶜ := fun z hz => (analytic z hz).continuousAt.continuousWithinAt
  have contg : ContinuousOn g (L.lattice : Set ℂ)ᶜ := by
    intro z hz
    have off : -z∉L.lattice := by simpa using hz
    exact (((analytic (-z) off).continuousAt.comp continuous_neg.continuousAt).neg).continuousWithinAt
  have dg (z : ℂ) (hz : z∉L.lattice) : HasDerivAt (fun w => F (-w)) (g z) z := by
    have off : -z∉L.lattice := by simpa using hz
    simpa only [g,manuscriptOmegaMinus,Function.comp_def,mul_neg,mul_one] using
      (dF (-z) off).comp z (hasDerivAt_id z).neg
  let B := fun z : ℂ => if z∈L.lattice then 0 else F z+F (-z)
  have bper (z ω : ℂ) (hω : ω∈L.lattice) : B (z+ω)=B z := by
    by_cases hz : z∈L.lattice
    · simp [B,hz,L.lattice.add_mem hz hω]
    · have shifted : z+ω∉L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h hω)
      obtain ⟨k,hk⟩ := translated_primitive_increment dF per hω
      have off : -(z+ω)∉L.lattice := by simpa only [neg_mem_iff] using shifted
      have reflected := hk _ off
      rw [show -(z+ω)+ω = -z by ring] at reflected
      simp only [B,ite_eq_right hz,ite_eq_right shifted]
      rw [hk z hz,reflected]
      ring
  let V := periodTorusLift L B bper
  have arcs (p : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ) :
      p.integral g=V p.finish.1-V p.start.1-p.integral f := by
    have hl := p.stays ⟨le_rfl,p.ordered⟩
    have hr := p.stays ⟨p.ordered,le_rfl⟩
    change p.integral g=B (p.curve p.right)-B (p.curve p.left)-p.integral f
    rw [arc_complex_primitive p contf dF,arc_complex_primitive p contg dg]
    change p.curve p.left∉L.lattice at hl
    change p.curve p.right∉L.lattice at hr
    simp only [B,ite_eq_right hr,ite_eq_right hl]; ring
  constructor
  · intro h
    simpa only [sub_self,zero_sub] using transfer_arc_integrals V arcs h
  · intro h
    have rev (p : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ) :
        p.integral f=V p.finish.1-V p.start.1-p.integral g := by
      rw [arcs]; ring
    simpa only [sub_self,zero_sub,neg_neg] using transfer_arc_integrals V rev h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_omega_gauss_height
#print axioms TwoAxisHelicoid.manuscript_horizontal_integral_negative
#print axioms TwoAxisHelicoid.manuscript_horizontal_periods_opposite
