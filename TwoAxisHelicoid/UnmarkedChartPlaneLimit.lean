import TwoAxisHelicoid.CompactCoreUnorientedNormalLimit
import TwoAxisHelicoid.RegularChartNormalStability

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology RealInnerProductSpace

private theorem core_normal_gap_neg_right (m N : SurfaceEuclideanSpace) :
    coreNormalDistance m (-N)=coreNormalDistance m N := by
  simp only [coreNormalDistance,sub_neg_eq_add,← sub_eq_add_neg,min_comm]

/-- Both signs of the normal are retained in the local limit when
positions converge and the tangent planes are uniformly close in an
ambient neighborhood of each limiting point, with no indexing of sheets. -/
theorem local_surface_normal_lifts_converge {B : Type*} {X N : B → SurfaceEuclideanSpace}
    {S : ℕ → Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace)}
    (symm : ∀ n y m, (y,m)∈S n → (y,-m)∈S n)
    (positions : LocalSpatialImageLimit (fun n => Prod.fst '' S n) (range X))
    (planes : ∀ b ε, 0<ε → ∃ W∈𝓝 (X b), ∀ᶠ n in atTop, ∀ q∈S n,
      q.1∈W → coreNormalDistance q.2 (N b)<ε) :
    LocalSpatialImageLimit S (unorientedSurfaceNormals X N) := by
  constructor
  · rintro ⟨y,t⟩ ⟨b,hy,ht⟩ V hv
    change X b=y at hy
    subst y
    change t=N b ∨ t= -N b at ht
    obtain ⟨ε,ep,sub⟩ := Metric.mem_nhds_iff.mp hv
    obtain ⟨W,wn,close⟩ := planes b ε ep
    have hits := positions.1 (X b) (mem_range_self b) (ball (X b) ε ∩ W) (inter_mem (ball_mem_nhds _ ep) wn)
    filter_upwards [hits,close] with n hit good
    obtain ⟨_,⟨⟨a,m⟩,hm,rfl⟩,ha,hw⟩ := hit
    have small : coreNormalDistance m (N b)<ε := good (a,m) hm hw
    have gap : coreNormalDistance m t<ε := by
      rcases ht with h|h
      · rwa [h]
      · rwa [h,core_normal_gap_neg_right]
    rcases (min_lt_iff.mp gap) with near|near
    · exact ⟨(a,m),hm,sub (show max (dist a (X b)) (dist m t)<ε from max_lt ha (by rwa [dist_eq_norm]))⟩
    · refine ⟨(a,-m),symm n a m hm,sub (show max (dist a (X b)) (dist (-m) t)<ε from max_lt ha ?_)⟩
      rwa [dist_eq_norm,show -m-t= -(m+t) by abel,norm_neg]
  · rintro ⟨y,m⟩ outside
    by_cases base : y∈range X
    · obtain ⟨b,rfl⟩ := base
      have ne : m≠N b := fun e => outside ⟨b,rfl,Or.inl e⟩
      have no : m+N b≠0 := fun e => outside ⟨b,rfl,Or.inr (eq_neg_of_add_eq_zero_left e)⟩
      let ε := coreNormalDistance m (N b)/2
      have positive : 0<coreNormalDistance m (N b) := lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr ne)) (norm_pos_iff.mpr no)
      obtain ⟨W,wn,bound⟩ := planes b ε (half_pos positive)
      let H := {q : SurfaceEuclideanSpace | ε<coreNormalDistance q (N b)}
      have cg : Continuous (fun q : SurfaceEuclideanSpace => coreNormalDistance q (N b)) :=
        (continuous_id.sub continuous_const).norm.min (continuous_id.add continuous_const).norm
      have hn : H∈𝓝 m := cg.continuousAt (lt_mem_nhds (half_lt_self positive))
      refine ⟨W ×ˢ H,prod_mem_nhds wn hn,?_⟩
      filter_upwards [bound] with n good using disjoint_left.mpr (fun q hq hin => (lt_asymm (good q hq hin.1) hin.2))
    · obtain ⟨V,hv,avoid⟩ := positions.2 y base
      refine ⟨Prod.fst ⁻¹' V,continuous_fst.continuousAt.preimage_mem_nhds hv,?_⟩
      filter_upwards [avoid] with n h using disjoint_left.mpr (fun q hq hin => disjoint_left.mp h ⟨q,hq,rfl⟩ hin)

/-- Convergence of ordinary derivatives of exhaustive local sheets
implies local convergence of the unmarked unit-normal sets. The charts
can vary with the sheet, the spatial point and the sequence index. -/
theorem unmarked_chart_derivatives_give_normal_limit {B : Type*} {X N : B → SurfaceEuclideanSpace}
    {S : ℕ → Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace)}
    (symm : ∀ n y m, (y,m)∈S n → (y,-m)∈S n)
    (unit : ∀ n (q : SurfaceEuclideanSpace × SurfaceEuclideanSpace), q∈S n → ‖q.2‖=1)
    (positions : LocalSpatialImageLimit (fun n => Prod.fst '' S n) (range X))
    (charts : ∀ b, ∃ T : ℂ →L[ℝ] SurfaceEuclideanSpace, Function.Injective T ∧ ‖N b‖=1 ∧
      (∀ v, ⟪T v,N b⟫=0) ∧ ∀ V∈𝓝 T, ∃ W∈𝓝 (X b), ∀ᶠ n in atTop, ∀ q∈S n, q.1∈W →
        ∃ (Y : ℂ → SurfaceEuclideanSpace) (w : ℂ), Y w=q.1 ∧ fderiv ℝ Y w∈V ∧ ∀ v, ⟪fderiv ℝ Y w v,q.2⟫=0) :
    LocalSpatialImageLimit S (unorientedSurfaceNormals X N) := by
  apply local_surface_normal_lifts_converge symm positions
  intro b ε ep
  obtain ⟨T,inj,un,pn,near⟩ := charts b
  obtain ⟨W,wn,en⟩ := near _ (nearby_regular_chart_normals inj un pn ep)
  refine ⟨W,wn,?_⟩
  filter_upwards [en] with n cover
  intro q hq hw
  obtain ⟨Y,w,_,der,orth⟩ := cover q hq hw
  exact der q.2 (unit n q hq) orth

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_surface_normal_lifts_converge
#print axioms TwoAxisHelicoid.unmarked_chart_derivatives_give_normal_limit
