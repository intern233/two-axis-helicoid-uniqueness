import TwoAxisHelicoid.ResidueFreeDoublePoleChange

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- The two Laurent coefficients of a differential with a double pole
are determined on its punctured germ. -/
theorem double_pole_laurent_expansion {h : ℂ → ℂ} (mer : MeromorphicAt h 0)
    (order : meromorphicOrderAt h 0=(-2:ℤ)) :
    ∃ (a b : ℂ) (P : ℂ → ℂ), a≠0 ∧ AnalyticAt ℂ P 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=a/z^2+b/z+P z := by
  obtain ⟨u,an,non,fac⟩ := (meromorphicOrderAt_eq_int_iff mer).mp order
  refine ⟨u 0,deriv u 0,dslope (dslope u 0) 0,non,analyticAt_dslope_center (analyticAt_dslope_center an),?_⟩
  filter_upwards [fac,self_mem_nhdsWithin] with z eq ne
  change z≠0 at ne
  have div : h z=u z/z^2 := by simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using eq
  rw [div]
  have s := sub_smul_dslope u 0 z
  have d := sub_smul_dslope (dslope u 0) 0 z
  simp only [sub_zero,smul_eq_mul,dslope_same] at s d
  field_simp [ne]
  linear_combination -s-z*d

theorem double_pole_laurent_coefficients_unique {a b c d : ℂ} {P Q : ℂ → ℂ}
    (cp : ContinuousAt P 0) (cq : ContinuousAt Q 0)
    (eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), a/z^2+b/z+P z=c/z^2+d/z+Q z) : a=c ∧ b=d := by
  have same : ∀ᶠ z in 𝓝[≠] (0:ℂ), a+z*b+z^2*P z=c+z*d+z^2*Q z := by
    filter_upwards [eq,self_mem_nhdsWithin] with z e ne
    change z≠0 at ne
    field_simp [ne] at e
    linear_combination e
  have lim (a b : ℂ) {F : ℂ → ℂ} (cont : ContinuousAt F 0) :
      Tendsto (fun z => a+z*b+z^2*F z) (𝓝[≠] 0) (𝓝 a) := by
    simpa [Pi.add_def,Pi.mul_def,Pi.pow_def,id_def] using ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).add
      ((continuousAt_id.pow 2).mul cont)).tendsto.mono_left nhdsWithin_le_nhds
  obtain rfl := tendsto_nhds_unique_of_eventuallyEq (lim a b cp) (lim c d cq) same
  have small : ∀ᶠ z in 𝓝[≠] (0:ℂ), b+z*P z=d+z*Q z := by
    filter_upwards [same,self_mem_nhdsWithin] with z e ne
    change z≠0 at ne
    apply mul_left_cancel₀ ne
    linear_combination e
  have first (b : ℂ) {F : ℂ → ℂ} (cont : ContinuousAt F 0) :
      Tendsto (fun z => b+z*F z) (𝓝[≠] 0) (𝓝 b) := by
    simpa [Pi.add_def,Pi.mul_def,id_def] using (continuousAt_const.add (continuousAt_id.mul cont)).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨rfl,tendsto_nhds_unique_of_eventuallyEq (first b cp) (first d cq) small⟩

/-- Pullback by an arbitrary regular local holomorphic parameter
preserves the residue, even when the residue is nonzero. -/
theorem double_pole_residue_change_coordinate {u h P : ℂ → ℂ} {a b : ℂ}
    (an : AnalyticAt ℂ u 0) (fixes : u 0=0) (unit : deriv u 0≠0) (pa : AnalyticAt ℂ P 0)
    (expansion : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=a/z^2+b/z+P z) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      deriv u z*h (u z)=(a/deriv u 0)/z^2+b/z+Q z := by
  let v := dslope u 0
  have va : AnalyticAt ℂ v 0 := analyticAt_dslope_center an
  have vn : v 0≠0 := (dslope_same u 0).trans_ne unit
  have mult : ∀ z : ℂ, z*v z=u z := fun z => by simpa only [sub_zero,smul_eq_mul,fixes] using sub_smul_dslope u 0 z
  have valid : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa only [fixes] using an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin,(va.continuousAt.eventually_ne vn).filter_mono nhdsWithin_le_nhds] with z hz nz
      exact (mult z) ▸ mul_ne_zero (show z≠0 from hz) nz
  let F := fun z : ℂ => a/z^2+P z
  obtain ⟨S,sa,reg⟩ := residue_free_double_pole_change_coordinate (u := u) (f := F)
    (P := fun z => deriv u z*F (u z)) an fixes unit pa (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => rfl)
  refine ⟨fun z => S z+b*(deriv v z/v z),sa.add (analyticAt_const.mul (va.deriv.div va vn)),?_⟩
  filter_upwards [reg,valid.eventually expansion,va.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (va.continuousAt.eventually_ne vn).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z e expz az nz ne
  change z≠0 at ne
  have du : deriv u z=v z+z*deriv v z := by
    rw [← funext mult]
    simpa only [id_eq,one_mul] using! ((hasDerivAt_id z).mul az.differentiableAt.hasDerivAt).deriv
  have log : deriv u z/u z=1/z+deriv v z/v z := by rw [du,← mult]; field_simp [ne,nz]
  change deriv u z*(a/(u z)^2+P (u z))=(a/deriv u 0)/z^2+S z at e
  rw [expz]
  linear_combination e+b*log

/-- If a regular holomorphic germ fixing the puncture acts by minus
one on a differential, the differential has zero residue there. -/
theorem negated_double_pole_has_zero_residue {h u : ℂ → ℂ}
    (mer : MeromorphicAt h 0) (order : meromorphicOrderAt h 0=(-2:ℤ))
    (an : AnalyticAt ℂ u 0) (fixes : u 0=0) (unit : deriv u 0≠0)
    (pull : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*h (u z)= -h z) :
    ∃ (a : ℂ) (P : ℂ → ℂ), a≠0 ∧ AnalyticAt ℂ P 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=a/z^2+P z := by
  obtain ⟨a,b,P,na,pa,expansion⟩ := double_pole_laurent_expansion mer order
  obtain ⟨Q,qa,tr⟩ := double_pole_residue_change_coordinate an fixes unit pa expansion
  have eq : ∀ᶠ z in 𝓝[≠] (0:ℂ), (a/deriv u 0)/z^2+b/z+Q z=(-a)/z^2+(-b)/z+(-P z) := by
    filter_upwards [pull,expansion,tr] with z e f d
    rw [← d,e,f]
    ring
  have res := (double_pole_laurent_coefficients_unique qa.continuousAt pa.continuousAt.neg eq).2
  have zero : b=0 := by linear_combination res/2
  exact ⟨a,P,na,pa,by simpa only [zero,zero_div,add_zero] using expansion⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.double_pole_residue_change_coordinate
#print axioms TwoAxisHelicoid.negated_double_pole_has_zero_residue
