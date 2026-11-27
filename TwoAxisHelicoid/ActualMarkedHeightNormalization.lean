import TwoAxisHelicoid.ActualMarkedLegendreRelation
import TwoAxisHelicoid.MarkedTorusNormalization
import TwoAxisHelicoid.AllComplexLatticePeriods

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- Full increments of the actual zeta series form an additive
character of the lattice, with no choice of path or base point. -/
noncomputable def markedZetaCharacter (L : PeriodPair) : L.lattice →+ ℂ where
  toFun w := markedZetaIncrement L w
  map_zero' := by simp [markedZetaIncrement]
  map_add' v w := by
    let b := L.ω₁/2
    have reg : b+(v:ℂ)∉L.lattice := fun h => L.ω₁_div_two_notMem_lattice
      (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h v.2)
    have step := marked_zeta_full_period L reg w.2
    change markedWeierstrassZeta L (b+((v:ℂ)+(w:ℂ)))-markedWeierstrassZeta L b=
      (markedWeierstrassZeta L (b+v)-markedWeierstrassZeta L b)+markedZetaIncrement L w
    rw [← step,← add_assoc]
    abel

noncomputable def markedHeightCharacter (L : PeriodPair) (A B : ℂ) : L.lattice →+ ℂ where
  toFun w := B*(w:ℂ)-A*markedZetaCharacter L w
  map_zero' := by simp
  map_add' v w := by simp only [Submodule.coe_add,map_add]; ring

private theorem marked_generator_characters_determine_real_periods (L : PeriodPair) (H : L.lattice →+ ℂ) :
    (∀ w, (H w).re=0) ↔
      (H ⟨L.ω₁,L.ω₁_mem_lattice⟩).re=0 ∧ (H ⟨L.ω₂,L.ω₂_mem_lattice⟩).re=0 := by
  constructor
  · exact fun all => ⟨all _,all _⟩
  · rintro ⟨one,two⟩ w
    let v₁ : L.lattice := ⟨L.ω₁,L.ω₁_mem_lattice⟩
    let v₂ : L.lattice := ⟨L.ω₂,L.ω₂_mem_lattice⟩
    obtain ⟨m,n,h⟩ := PeriodPair.mem_lattice.mp w.2
    have eqn : m • v₁+n • v₂=w := by
      apply Subtype.ext
      change m • L.ω₁+n • L.ω₂=(w:ℂ)
      simpa only [zsmul_eq_mul] using h
    rw [← eqn,map_add,map_zsmul,map_zsmul,Complex.add_re]
    change (m • H v₁).re+(n • H v₂).re=0
    have r (a : ℤ) (z : ℂ) : (a • z).re=(a:ℝ)*z.re := by simp [zsmul_eq_mul,Complex.mul_re]
    rw [r,r,show (H v₁).re=0 from one,show (H v₂).re=0 from two]
    ring

/-- The complex periods of a coefficient A℘+B on an arbitrary
marked punctured torus are exactly its zeta-character values. The
forward implication lifts the actual path; the reverse constructs a
piecewise smooth path in the lattice complement for every deck translation. -/
theorem marked_double_pole_actual_loop_periods (L : PeriodPair) {f : ℂ → ℂ} (A B : ℂ)
    (an : ∀ z∉L.lattice, DifferentiableAt ℂ f z)
    (per : ∀ z w, w∈L.lattice → f (z+w)=f z)
    (formula : ∀ z∉L.lattice, f z=A*L.weierstrassP z+B)
    (q : PuncturedPeriodTorus L) (v : ℂ) :
    (∃ γ : Path q q, TorusPathIntegral L f γ v) ↔ v∈range (markedHeightCharacter L A B) := by
  let F := fun z => -A*markedWeierstrassZeta L z+B*z
  have d (z : ℂ) (hz : z∉L.lattice) : HasDerivAt F (f z) z := by
    rw [formula z hz]
    convert ((marked_zeta_hasDerivAt L hz).const_mul (-A)).add ((hasDerivAt_id' z).const_mul B) using 1
    ring
  have mon (z : ℂ) (hz : z∉L.lattice) (w : L.lattice) : F (z+w)-F z=markedHeightCharacter L A B w := by
    change -A*markedWeierstrassZeta L (z+w)+B*(z+w)-(-A*markedWeierstrassZeta L z+B*z)=
      B*(w:ℂ)-A*markedZetaIncrement L w
    linear_combination -A*(marked_zeta_full_period L hz w.2)
  obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q.1
  have off : x∉L.lattice := fun h => q.2 (hx.symm.trans ((periodTorusProjection_eq_zero L x).mpr h))
  have cf : ContinuousOn f (L.lattice:Set ℂ)ᶜ := fun z hz => (an z hz).continuousAt.continuousWithinAt
  constructor
  · rintro ⟨γ,h⟩
    obtain ⟨y,hy,p,val⟩ := h.coherent_lift per x hx
    let w : L.lattice := ⟨y-x,(periodTorusProjection_eq_iff L x y).mp (hx.trans hy.symm)⟩
    have shifted : x+(w:ℂ)=y := by change x+(y-x)=y; ring
    exact ⟨w,by rw [← mon x off w,shifted,← p.integral_eq_primitive_sub cf d,val]⟩
  · rintro ⟨w,rfl⟩
    have reg : x+(w:ℂ)∉L.lattice := fun h => off (by simpa using L.lattice.sub_mem h w.2)
    have conn : IsPreconnected (L.lattice:Set ℂ)ᶜ :=
      (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_of_Lindelof_of_discrete (X:=L.lattice))).2
    obtain ⟨polygon⟩ := planePolygon_exists L.isClosed_lattice.isOpen_compl conn off reg
    obtain ⟨p,_⟩ := polygon.exists_piecewise_integral
    obtain ⟨ha,hb,γ,ig⟩ := p.projected_hasIntegral f
    have fromQ : q=puncturedPlaneProjection L ⟨x,ha⟩ := Subtype.ext hx.symm
    have toQ : q=puncturedPlaneProjection L ⟨x+w,hb⟩ :=
      Subtype.ext ((periodTorusProjection_add_lattice L x w w.2).trans hx).symm
    refine ⟨γ.cast fromQ toQ,?_⟩
    rw [← mon x off w,← p.integral_eq_primitive_sub cf d]
    exact ig.cast fromQ toQ

/-- Equation (C.1) in the arbitrary triangular marking of the
manuscript. Given the Laurent principal part, the coefficient has zero real
integral on every actual closed torus path if and only if it is the
displayed normalized Weierstrass differential. The zeta increments and
Legendre relation are both constructed from the actual lattice series. -/
theorem actual_marked_height_normalization (τ : ℂ) (upper : 0<τ.im) (A : ℂ) {f g : ℂ → ℂ}
    (an : ∀ z∉(upperMarkedLattice τ upper).lattice, DifferentiableAt ℂ f z)
    (periodic : ∀ z w, w∈(upperMarkedLattice τ upper).lattice → f (z+w)=f z)
    (regular : AnalyticAt ℂ g 0)
    (principal : ∀ᶠ z in 𝓝 (0:ℂ), z≠0 → f z=A/z^2+g z) :
    let L := upperMarkedLattice τ upper
    (∀ (q : PuncturedPeriodTorus L) (γ : Path q q) (v : ℂ), TorusPathIntegral L f γ v → v.re=0) ↔
      ∀ z∉L.lattice, f z=A*L.weierstrassP z+A*markedZetaIncrement L 1-
        2*Real.pi*I*((A.im/τ.im:ℝ):ℂ) := by
  let L := upperMarkedLattice τ upper
  let B := g 0
  let H := markedHeightCharacter L A B
  have coeff := elliptic_double_pole_classification L A an periodic regular principal
  have periods := marked_double_pole_actual_loop_periods L A B an periodic coeff
  have all : (∀ (q : PuncturedPeriodTorus L) (γ : Path q q) (v : ℂ), TorusPathIntegral L f γ v → v.re=0) ↔
      ∀ w : L.lattice, (H w).re=0 := by
    constructor
    · intro zero w
      let q := puncturedPlaneProjection L ⟨L.ω₁/2,L.ω₁_div_two_notMem_lattice⟩
      obtain ⟨γ,hγ⟩ := (periods q (H w)).mpr ⟨w,rfl⟩
      exact zero q γ (H w) hγ
    · intro zero q γ v hv
      obtain ⟨w,rfl⟩ := (periods q v).mp ⟨γ,hv⟩
      exact zero w
  have alg := marked_real_period_normalization (A:=A) (B:=B) upper (marked_full_quasiperiod_legendre τ upper)
  have roots := marked_generator_characters_determine_real_periods L H
  have two : (∀ w : L.lattice, (H w).re=0) ↔ B=A*markedZetaIncrement L 1-2*Real.pi*I*((A.im/τ.im:ℝ):ℂ) := by
    apply roots.trans
    change ((B*1-A*markedZetaIncrement L 1).re=0 ∧ (B*τ-A*markedZetaIncrement L τ).re=0) ↔ _
    rw [mul_one]
    exact alg
  change _ ↔ ∀ z∉L.lattice, _
  rw [all,two]
  constructor
  · intro eqn z hz
    change g 0=_ at eqn
    rw [coeff z hz,eqn]
    ring
  · intro formula
    have h := formula _ L.ω₁_div_two_notMem_lattice
    rw [coeff _ L.ω₁_div_two_notMem_lattice] at h
    change g 0=_
    linear_combination h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_double_pole_actual_loop_periods
#print axioms TwoAxisHelicoid.actual_marked_height_normalization
