import TwoAxisHelicoid.ActualTorusEndInjectivity
import TwoAxisHelicoid.ActualHeightInverse

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- The entire horizontal line in the complex height plane, at a
sufficiently large real part, is closedly embedded in the exterior disk. -/
theorem exterior_vertical_line_embedding {R h : ℝ} (large : R≤|h|) :
    IsClosedEmbedding (fun y : ℝ => (⟨(⟨h,y⟩:ℂ),large.trans (abs_re_le_norm (⟨h,y⟩:ℂ))⟩ :
      {z : ℂ // R≤‖z‖})) := by
  let e := fun y : ℝ => (⟨(⟨h,y⟩:ℂ),large.trans (abs_re_le_norm (⟨h,y⟩:ℂ))⟩ : {z : ℂ // R≤‖z‖})
  have c : Continuous e := Continuous.subtype_mk (Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)) _
  have inv : Function.LeftInverse (fun z : {z : ℂ // R≤‖z‖} => z.val.im) e := fun _ => rfl
  have ran : range e={z : {z : ℂ // R≤‖z‖} | z.val.re=h} := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      rfl
    · intro hz
      exact ⟨z.val.im,Subtype.ext (Complex.ext hz.symm rfl)⟩
  refine ⟨inv.isEmbedding (continuous_im.comp continuous_subtype_val) c,?_⟩
  change IsClosed (range e)
  rw [ran]
  exact isClosed_eq (continuous_re.comp continuous_subtype_val) continuous_const

/-- For the actual closed TwoAxisHelicoid immersion, every sufficiently high or
low horizontal plane cuts the whole surface in one properly embedded
line. The inverse height parameter traverses the whole torus fiber
exactly once. -/
theorem actual_high_horizontal_height_fibers {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z) :
    let L := rhombicPeriodPair t ht
    let H := actualComplexHeight t a c ht
    ∃ (K : ℂ → ℂ) (b A : ℝ), ∀ h : ℝ, A < |h| →
      (∀ y : ℝ, K ⟨h,y⟩∉L.lattice ∧ H (K ⟨h,y⟩)=⟨h,y⟩ ∧ X (K ⟨h,y⟩) 2=h+b) ∧
      IsClosedEmbedding (fun y : ℝ => X (K ⟨h,y⟩)) ∧
      (∀ z∉L.lattice, X z 2=h+b → ∃! y : ℝ,
        periodTorusProjection L (K ⟨h,y⟩)=periodTorusProjection L z) ∧
      Continuous (fun y : ℝ => K ⟨h,y⟩) := by
  let L := rhombicPeriodPair t ht
  let H := actualComplexHeight t a c ht
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X period q.1
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  obtain ⟨K,R,kLimit,kLeft,kRight,emb⟩ := actual_primitive_has_embedded_height_end ht ha hc diff
  obtain ⟨k,_,_,kk,kr,_,ka⟩ := actual_complex_height_inverse (a := a) ht hc
  have same : ∀ᶠ ξ : ℂ in cobounded ℂ, K ξ=k ξ⁻¹ := by
    filter_upwards [kk.eventually kLeft,kr] with ξ h₁ h₂
    rwa [h₂] at h₁
  have can : ∀ᶠ ξ : ℂ in cobounded ℂ, ContinuousAt K ξ := by
    obtain ⟨D,_,hd⟩ := hasBasis_cobounded_norm.eventually_iff.mp same
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop D,ka] with ξ hξ hka
    exact hka.continuousAt.congr_of_eventuallyEq (by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with v hv using hd hv.le)
  obtain ⟨D,_,outside⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    ((kLimit.eventually (rhombic_puncture_eventually_off_lattice ht)).and can)
  obtain ⟨b,height⟩ := actual_complex_height_real_primitive ht diff
  have prop : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ q : PuncturedPeriodTorus L, periodTorusProjection L z=q.1 →
      ∃ ξ : ℂ, K ξ∉L.lattice ∧ H (K ξ)=ξ ∧ periodTorusProjection L (K ξ)=q.1 := by
    filter_upwards [kLeft,rhombic_puncture_eventually_off_lattice ht] with z eq off
    intro q hq
    have e : K (H z)=z := eq
    exact ⟨H z,by rw [e]; exact off,congrArg H e,by rw [e]; exact hq⟩
  obtain ⟨C,hC,whole⟩ := compact_puncture_projected_property (π := periodTorusProjection L)
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap ((periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem) prop
  have cont : Continuous Y := periodTorusLift_continuous_punctured L X period (fun z hz => (diff z hz).continuousAt)
  obtain ⟨B,cb⟩ := hC.exists_bound_of_continuousOn (((continuous_apply 2).comp cont).sub (continuous_const (y := b))).continuousOn
  refine ⟨K,b,max (max R D) B,?_⟩
  intro h hh
  have large (y : ℝ) : max R D≤‖(⟨h,y⟩:ℂ)‖ :=
    ((le_max_left (max R D) B).trans hh.le).trans (abs_re_le_norm (⟨h,y⟩:ℂ))
  have off (y : ℝ) := (outside ((le_max_right R D).trans (large y))).1
  have val (y : ℝ) := kRight (⟨h,y⟩:ℂ) ((le_max_left R D).trans (large y))
  have line := emb.comp (exterior_vertical_line_embedding ((le_max_left R D).trans ((le_max_left _ B).trans hh.le)))
  refine ⟨fun y => ⟨off y,val y,(height _ (off y)).trans (congrArg (fun ξ : ℂ => ξ.re+b) (val y))⟩,line,?_,?_⟩
  · intro z hz level
    let q : PuncturedPeriodTorus L := ⟨periodTorusProjection L z,fun h => hz ((periodTorusProjection_eq_zero L z).mp h)⟩
    have Yq : Y q=X z := rfl
    have nC : q∉C := by
      intro hq
      have small : ‖Y q 2-b‖≤B := cb q hq
      rw [Yq,level,add_sub_cancel_right,Real.norm_eq_abs] at small
      exact (not_le_of_gt ((le_max_right (max R D) B).trans_lt hh)) small
    obtain ⟨ξ,nl,right,proj⟩ := whole q nC
    have image : X (K ξ)=X z := congrArg (periodTorusLift L X period) proj
    have re : ξ.re=h := by
      have v := height _ nl
      rw [image,level,show actualComplexHeight t a c ht (K ξ)=ξ from right] at v
      linarith
    have eq : (⟨h,ξ.im⟩:ℂ)=ξ := Complex.ext re.symm rfl
    refine ⟨ξ.im,?_,?_⟩
    · change periodTorusProjection L (K ⟨h,ξ.im⟩)=periodTorusProjection L z
      rwa [eq]
    · intro y hy
      apply line.injective
      change X (K ⟨h,y⟩)=X (K ⟨h,ξ.im⟩)
      rw [eq]
      exact congrArg (periodTorusLift L X period) (hy.trans proj.symm)
  · apply continuous_iff_continuousAt.mpr
    intro y
    exact ((outside ((le_max_right R D).trans (large y))).2).comp (Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_high_horizontal_height_fibers
