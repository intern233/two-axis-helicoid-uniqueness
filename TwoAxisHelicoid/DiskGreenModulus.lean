import TwoAxisHelicoid.ProperHolomorphicDiskCoordinate
import TwoAxisHelicoid.EqualModulusHolomorphicGerms
import TwoAxisHelicoid.UnitaryGermContinuation
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The exponential of the negative Dirichlet Green function:
its logarithm is harmonic away from the pole and differs from the
logarithm of the chart radius by a harmonic germ at the pole. -/
structure IsDiskGreenModulus {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (p : M) (ρ : M → ℝ) : Prop where
  nonneg : ∀ x, 0≤ρ x
  below_one : ∀ x, ρ x<1
  zero : ∀ x, ρ x=0 ↔ x=p
  boundary : Tendsto ρ (cocompact M) (𝓝 1)
  harmonic : ∀ x, x≠p → HarmonicAt (fun z => Real.log (ρ ((chartAt ℂ x).symm z))) (chartAt ℂ x x)
  pole : ∃ h : ℂ → ℝ, HarmonicAt h (chartAt ℂ p p) ∧ ∀ᶠ z in 𝓝 (chartAt ℂ p p),
    ρ ((chartAt ℂ p).symm z)=‖z-chartAt ℂ p p‖*Real.exp (h z)

private theorem real_harmonic_germ_has_conjugate {h : ℂ → ℝ} {a : ℂ} (hh : HarmonicAt h a) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ ∀ᶠ w in 𝓝 a, (H w).re=h w := by
  obtain ⟨r,rp,sub⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt h) a hh
  obtain ⟨H,an,eq⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f:=h) (z:=a) (R:=r) (fun _ hw => sub hw)
  refine ⟨H,an a (mem_ball_self rp),?_⟩
  filter_upwards [ball_mem_nhds a rp] with w hw using eq hw

/-- Local analytic functions with the prescribed Green modulus,
including a simple holomorphic zero in the pole chart. -/
theorem IsDiskGreenModulus.local_analytic {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    {p : M} {ρ : M → ℝ} (h : IsDiskGreenModulus p ρ) (x : M) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (chartAt ℂ x x) ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ x x), ‖g z‖=ρ ((chartAt ℂ x).symm z)) ∧
      (x=p → deriv g (chartAt ℂ x x)≠0) := by
  by_cases xp : x=p
  · subst x
    let a := chartAt ℂ p p
    obtain ⟨u,hu,form⟩ := h.pole
    obtain ⟨H,an,realPart⟩ := real_harmonic_germ_has_conjugate hu
    let g := fun z => (z-a)*Complex.exp (H z)
    refine ⟨g,(analyticAt_id.sub analyticAt_const).mul (an.cexp),?_,?_⟩
    · filter_upwards [form,realPart] with z hz reH
      simp only [g,norm_mul,Complex.norm_exp,reH,hz,a]
    · intro _
      have d := ((hasDerivAt_id a).sub_const a).mul (an.differentiableAt.hasDerivAt.cexp)
      change HasDerivAt g (1*Complex.exp (H a)+(a-a)*(Complex.exp (H a)*deriv H a)) a at d
      have eq : deriv g a=Complex.exp (H a) := by simpa using d.deriv
      rw [eq]
      exact Complex.exp_ne_zero _
  · let e := chartAt ℂ x
    have xs : x∈e.source := mem_chart_source ℂ x
    obtain ⟨H,an,reH⟩ := real_harmonic_germ_has_conjugate (h.harmonic x xp)
    have back : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by simpa only [e.left_inv xs] using (e.symm.continuousAt (e.map_source xs)).tendsto
    refine ⟨fun z => Complex.exp (H z),an.cexp,?_,fun eq => (xp eq).elim⟩
    filter_upwards [reH,back.eventually (isOpen_ne.mem_nhds xp)] with z hz ne
    rw [Complex.norm_exp,hz,Real.exp_log (lt_of_le_of_ne (h.nonneg _) (Ne.symm (mt (h.zero _).mp ne)))]

/-- The Green function determines one global holomorphic map. The
single logarithmic pole, its order and the actual boundary condition
force that map to be a bijection onto the disk. -/
theorem disk_coordinate_from_green_modulus {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : ℂ ≃ₜ M) {p : M} {ρ : M → ℝ} (h : IsDiskGreenModulus p ρ) :
    ∃ F : M → ℂ, ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F ∧ Injective F ∧ range F=ball (0:ℂ) 1 ∧ ∀ x, ‖F x‖=ρ x := by
  classical
  let _ : T2Space M := T.symm.isEmbedding.t2Space
  let _ : ContractibleSpace M := T.symm.contractibleSpace
  let _ : LocallyPathConnectedSpace M := T.locallyPathConnectedSpace
  choose g ag modG reg using h.local_analytic
  let f := fun x => g x ∘ chartAt ℂ x
  have near (x : M) : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (f x) y ∧ ‖f x y‖=ρ y := by
    let e := chartAt ℂ x
    have xs : x∈e.source := mem_chart_source ℂ x
    filter_upwards [e.open_source.mem_nhds xs,(e.continuousAt xs).eventually (ag x).eventually_analyticAt,
      (e.continuousAt xs).eventually (modG x)] with y ys an m
    exact ⟨an.contDiffAt.contMDiffAt.comp y (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) ys),m.trans (congrArg ρ (e.left_inv ys))⟩
  choose U valid op atX using fun x => mem_nhds_iff.mp (near x)
  have non (x y : M) (hy : y∈U x) : ¬ (∀ᶠ w in 𝓝 y, f x w=0) := by
    intro eq
    have only : ∀ᶠ w in 𝓝 y, w=p := by
      filter_upwards [eq,(op x).mem_nhds hy] with w hw wu
      exact (h.zero w).mp (((valid x wu).2.symm.trans (congrArg norm hw)).trans norm_zero)
    have yp := only.self_of_nhds
    have pull := T.continuous.continuousAt (x:=T.symm y)
    have t : ∀ᶠ w in 𝓝 (T.symm y), w=T.symm y := by
      have m : ∀ᶠ w in 𝓝 (T (T.symm y)), w=p := by rwa [T.apply_symm_apply]
      filter_upwards [pull.eventually m] with w hw using T.injective (hw.trans (yp.symm.trans (T.apply_symm_apply y).symm))
    have impossible : ∀ᶠ w in 𝓝[≠] (T.symm y), False := by
      filter_upwards [self_mem_nhdsWithin,t.filter_mono nhdsWithin_le_nhds] with w ne yes using ne yes
    exact impossible.exists.choose_spec
  obtain ⟨F,germ⟩ := simply_connected_glue_unitary_germs p U op id atX f (fun i j x hx =>
    equal_modulus_holomorphic_surface_germs (valid i hx.1).1 (valid j hx.2).1 (by
      filter_upwards [(op i).mem_nhds hx.1,(op j).mem_nhds hx.2] with w wi wj using
        (valid i wi).2.trans (valid j wj).2.symm) (non j x hx.2))
  have normF (x : M) : ‖F x‖=ρ x := by
    obtain ⟨c,eq⟩ := germ x x (atX x)
    rw [eq.self_of_nhds,norm_mul,Circle.norm_coe,one_mul,(valid x (atX x)).2]
  have hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F := by
    intro x
    obtain ⟨c,eq⟩ := germ x x (atX x)
    exact (contMDiffAt_const.mul (valid x (atX x)).1).congr_of_eventuallyEq eq
  have regular : deriv (F ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)≠0 := by
    let e := chartAt ℂ p
    have ps : p∈e.source := mem_chart_source ℂ p
    obtain ⟨c,eq⟩ := germ p p (atX p)
    have back : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by simpa only [e.left_inv ps] using (e.symm.continuousAt (e.map_source ps)).tendsto
    have locally : (F ∘ e.symm) =ᶠ[𝓝 (e p)] fun z => (c:ℂ)*g p z := by
      filter_upwards [back.eventually eq,e.open_target.mem_nhds (e.map_source ps)] with z hz ht
      change F (e.symm z)=(c:ℂ)*g p z
      change F (e.symm z)=(c:ℂ)*g p (e (e.symm z)) at hz
      rwa [e.right_inv ht] at hz
    rw [locally.deriv_eq,deriv_const_mul _ (ag p).differentiableAt]
    exact mul_ne_zero c.coe_ne_zero (reg p rfl)
  have sameNorm : (fun x => ‖F x‖)=ρ := funext normF
  obtain ⟨inj,onto⟩ := proper_holomorphic_disk_coordinate T hol (fun x => (normF x).trans_lt (h.below_one x))
    (sameNorm.symm ▸ h.boundary) p (fun x => by rw [← norm_eq_zero,normF,h.zero]) regular
  exact ⟨F,hol,inj,onto,normF⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_coordinate_from_green_modulus
