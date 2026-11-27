import TwoAxisHelicoid.PhysicalSliceLocalProjection
import TwoAxisHelicoid.CompactCoreUnorientedNormalLimit
import TwoAxisHelicoid.ConvergingCoreTubeCoverage

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A physical slice with a bijective foot projection is the graph of
one continuous signed displacement on the whole core. -/
theorem tube_single_sheet_is_physical_graph {B E : Type*} [TopologicalSpace B]
    {T : B × ℝ → E} {S : Set E} {R : ℝ}
    (homeo : IsHomeomorph (fun q : spatialTubeSlice T S R => q.1.1)) :
    ∃ h : B → ℝ, Continuous h ∧ (∀ b, |h b|<R) ∧
      spatialTubeSlice T S R=range (fun b => (b,h b)) := by
  let p := fun q : spatialTubeSlice T S R => q.1.1
  let e := homeo.isEmbedding.toHomeomorphOfSurjective homeo.surjective
  let h := fun b : B => (e.symm b).1.2
  refine ⟨h,continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous),fun b => (e.symm b).2.1,?_⟩
  ext q
  constructor
  · intro member
    let a : spatialTubeSlice T S R := ⟨q,member⟩
    exact ⟨q.1,Prod.ext rfl (congrArg (fun u : spatialTubeSlice T S R => u.1.2) (e.symm_apply_apply a))⟩
  · rintro ⟨b,rfl⟩
    have eq : (b,h b)=(e.symm b).1 := Prod.ext (e.apply_symm_apply b).symm rfl
    change (b,h b)∈spatialTubeSlice T S R
    rw [eq]
    exact (e.symm b).2

/-- On an open genus-one generating core, unmarked local convergence of
the physical positions and the unoriented tangent planes of embedded
handles produces a single global graph. Both the multiplicity and
local invertibility of the spatial projection are conclusions. -/
theorem unmarked_embedded_handles_form_one_core_graph {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    {B : Type*} [TopologicalSpace B] [T2Space B] {X N : B → SurfaceEuclideanSpace}
    (embed : IsClosedEmbedding X) (cn : Continuous N)
    {V : Set B} (vo : IsOpen V) (base : V ≃ₜ C.carrier) (kc : IsCompact (closure V))
    (regular : ∀ b∈closure V, ∃ a : OpenPartialHomeomorph B ℂ, b∈a.source ∧
      ContDiffAt ℝ 1 (X ∘ a.symm) (a b) ∧ ContDiffAt ℝ 1 (N ∘ a.symm) (a b) ∧
      Function.Injective (fderiv ℝ (X ∘ a.symm) (a b)) ∧ ‖N b‖=1 ∧
      ∀ v, ⟪fderiv ℝ (X ∘ a.symm) (a b) v,N b⟫=0)
    {U : Set B} {r : ℝ} (uo : IsOpen U) (ku : closure V⊆U) (rp : 0<r)
    (tube : IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict (fun q => X q.1+q.2 • N q.1)))
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] {L : ℕ → PeriodPair}
    (mark : ∀ n, M n ≃ₜ PuncturedPeriodTorus (L n)) (Y m : ∀ n, M n → SurfaceEuclideanSpace)
    (closed : ∀ n, IsClosedEmbedding (Y n)) (unit : ∀ n y, ‖m n y‖=1)
    (moving : ∀ n y, ∃ a : OpenPartialHomeomorph (M n) ℂ, y∈a.source ∧
      ContDiffAt ℝ 1 (Y n ∘ a.symm) (a y) ∧ Function.Injective (fderiv ℝ (Y n ∘ a.symm) (a y)) ∧
      ∀ v, ⟪fderiv ℝ (Y n ∘ a.symm) (a y) v,m n y⟫=0)
    (conv : LocalSpatialImageLimit (fun n => unorientedSurfaceNormals (Y n) (m n)) (unorientedSurfaceNormals X N)) :
    let TV := fun q : V × ℝ => X q.1.1+q.2 • N q.1.1
    ∃ R : ℝ, 0<R ∧ R<r ∧ (∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice TV (range (Y n)) R, |q.2|<ε) ∧
      ∀ᶠ n in atTop, IsHomeomorph (fun q : spatialTubeSlice TV (range (Y n)) R => q.1.1) ∧
        ∃ h : V → ℝ, Continuous h ∧ (∀ b, |h b|<R) ∧ spatialTubeSlice TV (range (Y n)) R=range (fun b => (b,h b)) := by
  intro TV
  let _ := C.pathConnected
  let _ : PreconnectedSpace V := (base.symm.surjective.connectedSpace base.symm.continuous).toPreconnectedSpace
  let T := fun q : B × ℝ => X q.1+q.2 • N q.1
  let S := fun n => unorientedSurfaceNormals (Y n) (m n)
  have ct : Continuous T := (embed.continuous.comp continuous_fst).add (continuous_snd.smul (cn.comp continuous_fst))
  have zero (b : B) : T (b,0)=X b := by simp [T]
  have units (n : ℕ) (q : SurfaceEuclideanSpace × SurfaceEuclideanSpace) (hq : q∈S n) : ‖q.2‖=1 := by
    obtain ⟨b,_,plus|minus⟩ := hq
    · rw [plus,unit]
    · rw [minus,norm_neg,unit]
  have pos := unoriented_normals_project_to_image_limit embed.isClosed_range units conv
  have images (n : ℕ) : Prod.fst '' S n=range (Y n) := by
    ext z
    constructor
    · rintro ⟨q,⟨b,atb,_⟩,rfl⟩
      exact ⟨b,atb⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(Y n b,m n b),⟨b,rfl,Or.inl rfl⟩,rfl⟩
  have spatial : LocalSpatialImageLimit (fun n => range (Y n)) (range X) := by simpa only [images] using pos
  have ne : V.Nonempty := ⟨(base.symm C.base).1,(base.symm C.base).2⟩
  obtain ⟨R,positive,small,thin,cover⟩ := convergent_embedded_core_tube_exhaustion embed ct zero vo ne kc uo ku rp tube
    (fun n => (closed n).isClosed_range) spatial
  obtain ⟨a,ap,feet⟩ := compact_physical_foot_charts kc regular
  obtain ⟨W,s,_,includeK,_,sp,iso⟩ := closed_surface_tube_meets_only_zero embed ct zero kc uo ku rp tube
  have normals := unoriented_normal_limit_uniform_on_core_tube embed.injective cn units conv ct zero kc
    (fun b hb t ht im => (iso b (includeK hb) t ht).mp im) (half_lt_self sp) 1 zero_lt_one
  have tubeV := compact_core_subtube_open_embedding vo (fun b hb => ku (subset_closure hb)) small.le tube
  refine ⟨R,positive,small,thin,?_⟩
  filter_upwards [cover,thin a ap,thin (s/2) (half_pos sp),normals] with n useful low collar angles
  have loc : IsLocalHomeomorph (fun q : spatialTubeSlice TV (range (Y n)) R => q.1.1) := by
    apply physical_tube_slice_local_homeomorph vo (closed n).isEmbedding tubeV
    · intro q hq
      exact feet q.1.1 (subset_closure q.1.2) q.2 (low q hq)
    · intro q hq y eq
      obtain ⟨e,ey,se,im,perp⟩ := moving n y
      exact ⟨e,m n y,ey,se,im,unit n y,perp,
        angles q.1.1 (subset_closure q.1.2) q.2 (collar q hq).le (m n y) ⟨y,eq,Or.inl rfl⟩⟩
  have one := physical_genus_one_tube_single_sheet C base (mark n) tubeV (closed n).isEmbedding useful.1 useful.2.1 loc
  exact ⟨one,tube_single_sheet_is_physical_graph one⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.tube_single_sheet_is_physical_graph
#print axioms TwoAxisHelicoid.unmarked_embedded_handles_form_one_core_graph
