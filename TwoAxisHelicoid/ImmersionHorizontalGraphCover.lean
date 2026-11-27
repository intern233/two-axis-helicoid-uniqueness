import TwoAxisHelicoid.HorizontalGraphHeightChart
import Mathlib.Topology.Compactness.Lindelof

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- The linear height whose level planes have horizontal slope s. -/
noncomputable def tiltedSpatialHeight (s : ℂ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 2-(innerSL ℝ s).comp (spatialGraphProjection 0 1)

theorem tilted_contact_iff {F : ℂ → Fin 3 → ℝ} {z : ℂ} (df : DifferentiableAt ℝ F z) (s : ℂ) :
    fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0 ↔
      ∀ v, fderiv ℝ F z v 2=⟪s,spatialGraphProjection 0 1 (fderiv ℝ F z v)⟫_ℝ := by
  rw [((tiltedSpatialHeight s).hasFDerivAt.comp z df.hasFDerivAt).fderiv]
  constructor
  · intro zero v
    exact sub_eq_zero.mp (DFunLike.congr_fun zero v)
  · intro equal
    ext v
    exact sub_eq_zero.mpr (equal v)

/-- On an arbitrary subset of a parametrized surface, countably many
actual horizontal graph charts cover every contact with a plane of finite
slope. Regularity is needed only at that subset, allowing a missing
point of the torus marking. -/
theorem countable_horizontal_graph_contact_cover {D : Set ℂ} {F : ℂ → Fin 3 → ℝ}
    (smooth : ∀ z∈D, ContDiffAt ℝ 3 F z)
    (imm : ∀ z∈D, Function.Injective (fderiv ℝ F z)) :
    let P := spatialGraphProjection 0 1
    ∃ C : Set {z : ℂ // z∈D ∧ Function.Injective (P.comp (fderiv ℝ F z))}, C.Countable ∧
      ∃ (W : C → Set ℂ) (f : C → ℂ → ℝ),
        (∀ i x, x∈W i → ContDiffAt ℝ 3 (f i) x) ∧
        ∀ s z, z∈D → fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0 →
          ∃ i : C, P (F z)∈W i ∧ f i (P (F z))=F z 2 ∧ gradient (f i) (P (F z))=s ∧
            ∃ e : OpenPartialHomeomorph ℂ ℂ, z∈e.source ∧
              (∀ y, e y=P (F y)) ∧ ContDiffAt ℝ 3 e z ∧ ContDiffAt ℝ 3 e.symm (e z) ∧
              ∀ᶠ y in 𝓝 z, F y 2=f i (e y) := by
  classical
  intro P
  let A := {z : ℂ | z∈D ∧ Function.Injective (P.comp (fderiv ℝ F z))}
  choose e f U op base source projection reg form using fun q : A =>
    horizontal_graph_height_chart (smooth q.1 q.2.1) q.2.2
  obtain ⟨C,ct,covers⟩ := TopologicalSpace.countable_cover_nhds (fun q : A =>
    ((op q).preimage continuous_subtype_val).mem_nhds (show q∈(Subtype.val : A → ℂ) ⁻¹' U q from base q))
  refine ⟨C,ct,fun i => e i.1 '' U i.1,fun i => f i.1,?_,?_⟩
  · rintro i _ ⟨y,hy,rfl⟩
    exact (reg i.1 y hy).2.2
  · intro s z hz contact
    have df := ((smooth z hz).differentiableAt (by norm_num)).hasFDerivAt
    have critical := (tilted_contact_iff df.differentiableAt s).mp contact
    have ji := horizontal_projection_injective_at_height_contact (imm z hz) s critical
    let point : A := ⟨z,hz,ji⟩
    obtain ⟨q,hq,zq⟩ := mem_iUnion₂.mp
      (show point∈⋃ q∈C, (Subtype.val : A → ℂ) ⁻¹' U q from covers.symm ▸ mem_univ _)
    have inU : z∈U q := zq
    obtain ⟨de,back,du⟩ := reg q z inU
    have eq : (fun w => F w 2) =ᶠ[𝓝 z] f q ∘ e q :=
      Filter.mem_of_superset ((op q).mem_nhds inU) (fun w h => form q w h)
    have eEq : (e q : ℂ → ℂ)=P ∘ F := funext (projection q)
    have dp : HasFDerivAt (e q) (P.comp (fderiv ℝ F z)) z := eEq.symm ▸ P.hasFDerivAt.comp z df
    let vert := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 2
    have eqD : vert.comp (fderiv ℝ F z)=(fderiv ℝ (f q) (e q z)).comp (P.comp (fderiv ℝ F z)) :=
      (vert.hasFDerivAt.comp z df).fderiv.symm.trans
        ((eq.fderiv_eq (𝕜:=ℝ)).trans ((du.differentiableAt (by norm_num)).hasFDerivAt.comp z dp).fderiv)
    have slope : gradient (f q) (e q z)=s := by
      apply (toDual ℝ ℂ).injective
      ext v
      obtain ⟨a,ha⟩ := (LinearMap.injective_iff_surjective (f:=((P.comp (fderiv ℝ F z)).toLinearMap))).mp ji v
      change (P.comp (fderiv ℝ F z)) a=v at ha
      have coord := DFunLike.congr_fun eqD a
      change fderiv ℝ F z a 2=fderiv ℝ (f q) (e q z) ((P.comp (fderiv ℝ F z)) a) at coord
      rw [toDual_gradient,toDual_apply_apply,← ha,← coord]
      exact critical a
    refine ⟨⟨q,hq⟩,⟨z,inU,projection q z⟩,?_,?_,e q,source q inU,projection q,de,back,eq⟩
    · rw [← projection q z]
      exact (form q z inU).symm
    · rwa [← projection q z]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.countable_horizontal_graph_contact_cover
