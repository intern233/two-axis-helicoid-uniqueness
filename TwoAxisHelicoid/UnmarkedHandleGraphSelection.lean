import TwoAxisHelicoid.MarkedPhysicalCoreGraph

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- The compact genus-one core selects a single actual open embedding
into each moving handle on a common tail. The unoriented normal angles
and signed heights vanish uniformly on the whole open core. -/
theorem unmarked_handles_select_transverse_core_graphs {A : PeriodPair} (C : TorusGeneratingCoreModel A)
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
    ∃ R : ℝ, 0<R ∧ R<r ∧ ∃ k : ℕ, ∃ G : ∀ n, PhysicalCoreGraph TV (Y (n+k)) R,
      (∀ n b, coreNormalDistance (m (n+k) ((G n).point b)) (N b.1)<1) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ b, |(G n).height b|<ε ∧
        coreNormalDistance (m (n+k) ((G n).point b)) (N b.1)<ε := by
  intro TV
  obtain ⟨R,positive,small,thin,homeos⟩ := unmarked_embedded_handles_form_one_core_graph C embed cn vo base kc
    regular uo ku rp tube mark Y m closed unit moving conv
  let T := fun q : B × ℝ => X q.1+q.2 • N q.1
  have ct : Continuous T := (embed.continuous.comp continuous_fst).add (continuous_snd.smul (cn.comp continuous_fst))
  have zero (b : B) : T (b,0)=X b := by simp [T]
  obtain ⟨_,s,_,inc,_,sp,iso⟩ := closed_surface_tube_meets_only_zero embed ct zero kc uo ku rp tube
  have units (n : ℕ) (q : SurfaceEuclideanSpace × SurfaceEuclideanSpace) (hq : q∈unorientedSurfaceNormals (Y n) (m n)) :
      ‖q.2‖=1 := by
    obtain ⟨y,_,hp|hm⟩ := hq
    · rw [hp,unit]
    · rw [hm,norm_neg,unit]
  have bound := unoriented_normal_limit_uniform_on_core_tube embed.injective cn units conv ct zero kc
    (fun b hb t ht im => (iso b (inc hb) t ht).mp im) (half_lt_self sp)
  have openV := compact_core_subtube_open_embedding vo (fun b hb => ku (subset_closure hb)) small.le tube
  refine ⟨R,positive,small,select_transverse_physical_core_graphs (N := fun b : V => N b.1) openV
    (fun n => (closed n).isEmbedding) (homeos.mono (fun _ h => h.1)) thin ?_⟩
  intro ε ep
  filter_upwards [thin (s/2) (half_pos sp),bound ε ep] with n low angle q hq y eq
  exact angle q.1.1 (subset_closure q.1.2) q.2 (low q hq).le (m n y) ⟨y,eq,Or.inl rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_handles_select_transverse_core_graphs
