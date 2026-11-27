import TwoAxisHelicoid.DiskFiberWinding
import TwoAxisHelicoid.HolomorphicLocalWinding
import TwoAxisHelicoid.PlaneCoverChartOrientation
import TwoAxisHelicoid.HolomorphicSurfaceIdentity

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology
open scoped Topology ContDiff Manifold

/-- A disk-valued holomorphic map on an abstract topological plane
with boundary modulus tending to one is a global coordinate if it has
exactly one zero and this zero is simple. All other multiplicities
are determined by winding on a large circle in the topological marking. -/
theorem proper_holomorphic_disk_coordinate {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : ℂ ≃ₜ M) {f : M → ℂ} (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (unit : ∀ x, ‖f x‖<1) (escape : Tendsto (fun x => ‖f x‖) (cocompact M) (𝓝 1))
    (p : M) (zero : ∀ y, f y=0 ↔ y=p)
    (regular : deriv (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)≠0) :
    Injective f ∧ range f=ball (0:ℂ) 1 := by
  classical
  let _ : ContractibleSpace M := T.symm.contractibleSpace
  let F := f ∘ T
  let q := T.symm p
  have ct : Continuous F := hol.continuous.comp T.continuous
  have bd : Tendsto (fun z => ‖F z‖) (cocompact ℂ) (𝓝 1) := escape.comp T.isClosedEmbedding.tendsto_cocompact
  have zz (z : ℂ) : F z=0 ↔ z=q := (zero _).trans T.toEquiv.eq_symm_apply.symm
  have chartAn (x : M) {w : ℂ} (hw : w∈(chartAt ℂ x).target) : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) w :=
    ((hol _).comp w (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) x) hw)).contDiffAt.analyticAt
  have non (x : M) : ¬ (∀ᶠ y in 𝓝 x, f y=f x) := by
    intro constant
    have allX := holomorphic_surface_constant_of_germ hol constant
    have fp := (zero p).mpr rfl
    have c := (allX p).symm.trans fp
    have v := (zero (T (q+1))).mp ((allX _).trans c)
    have e : q+1=q := T.injective (v.trans (T.apply_symm_apply p).symm)
    exact one_ne_zero (add_eq_left.mp e)
  have notLocal (z : ℂ) (a := chartAt ℂ (T z)) (src : T z∈a.source) :
      ¬ (∀ᶠ w in 𝓝 (a (T z)), f (a.symm w)=f (T z)) := by
    intro constant
    apply non (T z)
    filter_upwards [a.open_source.mem_nhds src,(a.continuousAt src).eventually constant] with y hy h
    rwa [a.left_inv hy] at h
  obtain ⟨s,sign,orient⟩ := complex_surface_plane_cover_orientation T.isLocalHomeomorph
  have each (z : ℂ) : ∃ k : ℕ, HasPlaneOrientationAt F z (((k+1:ℕ):ℤ)*s) ∧ (z=q → k=0) := by
    let a := chartAt ℂ (T z)
    let e := T.toOpenPartialHomeomorph.trans a
    let g := f ∘ a.symm
    have src : T z∈a.source := mem_chart_source ℂ _
    have es : z∈e.source := ⟨trivial,src⟩
    have an : AnalyticAt ℂ g (e z) := chartAn _ (a.map_source src)
    have val : g (e z)=f (T z) := congrArg f (a.left_inv src)
    have germ : F =ᶠ[𝓝 z] g ∘ e := by
      filter_upwards [T.continuous.continuousAt.eventually (a.open_source.mem_nhds src)] with y hy
      exact (congrArg f (a.left_inv hy)).symm
    let n := analyticOrderAt (fun w => g w-g (e z)) (e z)
    have fin : n≠⊤ := by
      intro h
      exact notLocal z a src ((analyticOrderAt_eq_top.mp h).mono fun _ eq => (sub_eq_zero.mp eq).trans val)
    obtain ⟨m,hm⟩ : ∃ m : ℕ, n=(m:ℕ∞) := ⟨n.toNat,(ENat.natCast_toNat_eq_self.mpr fin).symm⟩
    cases m with
    | zero => exact (((an.sub analyticAt_const).analyticOrderAt_eq_zero.mp hm) (sub_self _)).elim
    | succ k =>
      refine ⟨k,(local_holomorphic_order_winding e es (orient z (T z) src) an hm).congr germ,?_⟩
      intro eq
      have base : T z=p := eq ▸ T.apply_symm_apply p
      have dr : deriv g (e z)≠0 := by change deriv (f ∘ (chartAt ℂ (T z)).symm) (chartAt ℂ (T z) (T z))≠0; rwa [base]
      have ord := an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero dr
      change n=1 at ord
      rw [hm] at ord
      exact_mod_cast (show k+1=1 by exact_mod_cast ord) |> Nat.succ_inj.mp
  choose k ori ks using each
  have fibers (c : ℂ) (hc : ‖c‖<1) : (F ⁻¹' {c}).Finite := by
    obtain ⟨K,compact,away⟩ := hasBasis_cocompact.mem_iff.mp (bd.eventually (lt_mem_nhds hc))
    have inK : F ⁻¹' {c}⊆K := fun z hz => by
      by_contra out
      have h := away out
      change ‖c‖<‖F z‖ at h
      change F z=c at hz
      exact h.ne (congrArg norm hz).symm
    have cl : IsClosed (F ⁻¹' {c}) := isClosed_singleton.preimage ct
    apply (compact.of_isClosed_subset cl inK).finite
    apply isDiscrete_iff_nhdsNE.mpr
    intro z hz
    rw [inf_principal_eq_bot]
    let a := chartAt ℂ (T z)
    let e := T.toOpenPartialHomeomorph.trans a
    have src : T z∈a.source := mem_chart_source ℂ _
    have es : z∈e.source := ⟨trivial,src⟩
    obtain loc|iso := (chartAn (T z) (a.map_source src)).eventually_eq_or_eventually_ne (analyticAt_const (v:=c))
    · exact (notLocal z a src (loc.mono fun _ h => h.trans (show f (T z)=c from hz).symm)).elim
    · have nt : Tendsto e (𝓝[≠] z) (𝓝[≠] (e z)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(e.continuousAt es).tendsto.mono_left nhdsWithin_le_nhds,?_⟩
        filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds es)] with y ne ys
        exact fun eq => ne (e.injOn ys es eq)
      filter_upwards [nt.eventually iso,mem_nhdsWithin_of_mem_nhds
        (T.continuous.continuousAt.eventually (a.open_source.mem_nhds src))] with y h ys
      exact fun eq => h ((congrArg f (a.left_inv ys)).trans eq)
  obtain ⟨fi,onto⟩ := single_simple_zero_disk_bijection ct (fun z => unit (T z)) bd fibers (by rcases sign with h|h <;> omega)
    k ori q zz (ks q rfl)
  refine ⟨fun x y eq => T.symm.injective (fi (a₁:=T.symm x) (a₂:=T.symm y) (by simpa [F] using eq)),?_⟩
  rwa [image_univ,show range F=range f from by rw [show F=f ∘ T from rfl,range_comp,T.surjective.range_eq,image_univ]] at onto

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.proper_holomorphic_disk_coordinate
