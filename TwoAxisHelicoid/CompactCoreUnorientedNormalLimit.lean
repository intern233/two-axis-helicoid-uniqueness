import TwoAxisHelicoid.EmbeddedCoreTubeIsolation
import TwoAxisHelicoid.CoreSheetPlaneConvergence
import TwoAxisHelicoid.TransverseCoreTubeSheets

namespace TwoAxisHelicoid
open Set Filter Topology Metric
open scoped Topology RealInnerProductSpace

/-- The two unit normals above each point of a parametrized surface. -/
def unorientedSurfaceNormals {B : Type*} (X N : B → SurfaceEuclideanSpace) :
    Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace) :=
  {q | ∃ b, X b=q.1 ∧ (q.2=N b ∨ q.2= -N b)}

/-- Local convergence of the positions and their unoriented normals
implies local convergence of the underlying closed spatial images. -/
theorem unoriented_normals_project_to_image_limit {B : Type*} {X N : B → SurfaceEuclideanSpace}
    (closed : IsClosed (range X)) {S : ℕ → Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace)}
    (unit : ∀ n (q : SurfaceEuclideanSpace × SurfaceEuclideanSpace), q∈S n → ‖q.2‖=1)
    (conv : LocalSpatialImageLimit S (unorientedSurfaceNormals X N)) :
    LocalSpatialImageLimit (fun n => Prod.fst '' S n) (range X) := by
  constructor
  · rintro _ ⟨b,rfl⟩ V nv
    have h := conv.1 (X b,N b) ⟨b,rfl,Or.inl rfl⟩ (Prod.fst ⁻¹' V) (continuous_fst.continuousAt.preimage_mem_nhds nv)
    filter_upwards [h] with n hit
    obtain ⟨q,hq,hv⟩ := hit
    exact ⟨q.1,⟨q,hq,rfl⟩,hv⟩
  · intro x outside
    obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (closed.isOpen_compl.mem_nhds outside)
    let R := r/2
    have pos : 0<R := half_pos rp
    let K := closedBall x R ×ˢ sphere (0:SurfaceEuclideanSpace) 1
    have compact : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
    have avoid : Disjoint K (unorientedSurfaceNormals X N) := by
      apply disjoint_left.mpr
      rintro q hq ⟨b,eq,_⟩
      exact (sub (closedBall_subset_ball (half_lt_self rp) hq.1)) ⟨b,eq⟩
    refine ⟨ball x R,ball_mem_nhds _ pos,?_⟩
    filter_upwards [conv.eventually_disjoint_compact compact avoid] with n separate
    apply disjoint_left.mpr
    rintro _ ⟨q,hq,rfl⟩ near
    exact disjoint_left.mp separate hq ⟨ball_subset_closedBall near,by simpa only [mem_sphere,dist_zero_right] using unit n q hq⟩

/-- Every actual sheet in an inner tube over a fixed compact core has a
normal uniformly close to one of the two reference normals. This only
requires convergence of the unmarked sets of point-normal pairs and
isolation of the zero sheet of the limit. -/
theorem unoriented_normal_limit_uniform_on_core_tube {B : Type*} [TopologicalSpace B]
    {X N : B → SurfaceEuclideanSpace} (inj : Function.Injective X) (cn : Continuous N)
    {S : ℕ → Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace)}
    (unit : ∀ n (q : SurfaceEuclideanSpace × SurfaceEuclideanSpace), q∈S n → ‖q.2‖=1)
    (conv : LocalSpatialImageLimit S (unorientedSurfaceNormals X N))
    {T : B × ℝ → SurfaceEuclideanSpace} (ct : Continuous T) (zero : ∀ b, T (b,0)=X b)
    {K : Set B} (kc : IsCompact K) {r : ℝ}
    (isolate : ∀ b∈K, ∀ t : ℝ, |t|<r → T (b,t)∈range X → t=0) {R : ℝ} (inner : R<r) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ b∈K, ∀ t : ℝ, |t|≤R → ∀ m : SurfaceEuclideanSpace,
      (T (b,t),m)∈S n → coreNormalDistance m (N b)<ε := by
  intro ε ep
  let P := (K ×ˢ Icc (-R) R) ×ˢ sphere (0:SurfaceEuclideanSpace) 1
  let D := P ∩ {q : (B × ℝ) × SurfaceEuclideanSpace | ε≤coreNormalDistance q.2 (N q.1.1)}
  let F := fun q : (B × ℝ) × SurfaceEuclideanSpace => (T q.1,q.2)
  have cN : Continuous (fun q : (B × ℝ) × SurfaceEuclideanSpace => N q.1.1) := cn.comp (continuous_fst.comp continuous_fst)
  have cd : Continuous (fun q : (B × ℝ) × SurfaceEuclideanSpace => coreNormalDistance q.2 (N q.1.1)) :=
    ((continuous_snd.sub cN).norm).min ((continuous_snd.add cN).norm)
  have compact : IsCompact D := ((kc.prod isCompact_Icc).prod (isCompact_sphere _ _)).inter_right (isClosed_le continuous_const cd)
  have cf : Continuous F := (ct.comp continuous_fst).prodMk continuous_snd
  have avoid : Disjoint (F '' D) (unorientedSurfaceNormals X N) := by
    apply disjoint_left.mpr
    rintro _ ⟨⟨⟨b,t⟩,m⟩,hb,rfl⟩ ⟨a,foot,plane⟩
    change X a=T (b,t) at foot
    have ht := isolate b hb.1.1.1 t ((abs_le.mpr hb.1.1.2).trans_lt inner) ⟨a,foot⟩
    subst t
    rw [zero] at foot
    obtain rfl := inj foot
    have low : ε≤min ‖m-N a‖ ‖m+N a‖ := hb.2
    change m=N a ∨ m= -N a at plane
    rcases plane with p|p
    · rw [p,sub_self,norm_zero] at low
      exact ep.not_ge (low.trans (min_le_left _ _))
    · rw [p,neg_add_cancel,norm_zero] at low
      exact ep.not_ge (low.trans (min_le_right _ _))
  filter_upwards [conv.eventually_disjoint_compact (compact.image cf) avoid] with n disj
  intro b hb t ht m member
  by_contra! bad
  apply disjoint_left.mp disj member
  refine ⟨((b,t),m),⟨⟨⟨hb,abs_le.mp ht⟩,?_⟩,bad⟩,rfl⟩
  simpa only [mem_sphere,dist_zero_right] using unit n (T (b,t),m) member

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unoriented_normals_project_to_image_limit
#print axioms TwoAxisHelicoid.unoriented_normal_limit_uniform_on_core_tube
