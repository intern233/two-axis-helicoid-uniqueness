import TwoAxisHelicoid.ProperLocalCover
import TwoAxisHelicoid.FiniteNormalGraphSheets
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.EquivFin

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- Part of a closed spatial surface in an open tube, written in its
actual base and signed-height coordinates. -/
def spatialTubeSlice {B E : Type*} (T : B × ℝ → E) (S : Set E) (r : ℝ) : Set (B × ℝ) :=
  {x | |x.2|<r ∧ T x∈S}

/-- When all sheets in the open tube avoid its outer collar, projection
of their union is proper over the whole base. The base may be open
and noncompact. -/
theorem compact_height_slab_projection_proper {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {T : B × ℝ → E} (ct : Continuous T) {S : Set E} (closed : IsClosed S) {r s : ℝ} (gap : s<r)
    (bound : ∀ q∈spatialTubeSlice T S r, |q.2|≤s) :
    IsProperMap (fun q : spatialTubeSlice T S r => q.1.1) := by
  let I := Icc (-s) s
  let J := fun q : B × I => (q.1,q.2.1)
  have cj : Continuous J := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  let C := J ⁻¹' (T ⁻¹' S)
  have cc : IsClosed C := (closed.preimage ct).preimage cj
  let H : spatialTubeSlice T S r ≃ₜ C := {
    toFun := fun q => ⟨(q.1.1,⟨q.1.2,abs_le.mp (bound _ q.2)⟩),q.2.2⟩
    invFun := fun q => ⟨J q.1,(abs_le.mpr q.1.2.2).trans_lt gap,q.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := (cj.comp continuous_subtype_val).subtype_mk _ }
  let _ : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have project : IsProperMap (Prod.fst : B × I → B) := isProperMap_fst_of_compactSpace
  exact project.comp (cc.isClosedEmbedding_subtypeVal.isProperMap.comp H.isProperMap)

/-- Finite exhaustive local sheets can be chosen from a proper local
homeomorphism onto the base. They need not be globally labelled. -/
theorem finite_sheet_germs_of_proper_projection {A B : Type*} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    {p : A → B} (proper : IsProperMap p) (loc : IsLocalHomeomorph p) (onto : Function.Surjective p)
    (b : B) : Nonempty (FiniteSheetGerms p b) := by
  classical
  let F := p ⁻¹' {b}
  obtain ⟨a,ha⟩ := onto b
  let _ : Nonempty F := ⟨⟨a,ha⟩⟩
  let _ : Fintype F := (proper_local_homeomorph_finite_fibers proper loc b).fintype
  let n := Fintype.card F-1
  have eq : Fintype.card F=n+1 := by dsimp [n]; have h := Fintype.card_pos (α := F); omega
  let idx : Fin (n+1) ≃ F := (Fintype.equivFinOfCardEq eq).symm
  obtain ⟨_,U,bu,op,_,H,hp⟩ := proper_local_homeomorph_isCoveringMap proper loc b
  let sheet := fun (i : Fin (n+1)) (y : B) => if hy : y∈U then (H.symm (⟨y,hy⟩,idx i)).1 else (idx i).1
  have germ (i : Fin (n+1)) (y : U) : sheet i y=(H.symm (y,idx i)).1 := dite_eq_left y.2
  refine ⟨⟨n,sheet,?_,?_,?_⟩⟩
  · intro i
    apply ContinuousOn.continuousAt (s := U) _ (op.mem_nhds bu)
    apply continuousOn_iff_continuous_domRestrict.mpr
    have e : U.domRestrict (sheet i)=(fun y : U => (H.symm (y,idx i)).1) := funext (germ i)
    rw [e]
    fun_prop
  · intro i j h
    have e : H.symm (⟨b,bu⟩,idx i)=H.symm (⟨b,bu⟩,idx j) := Subtype.ext (by simpa only [sheet,dite_eq_left bu] using h)
    exact idx.injective (congrArg Prod.snd (H.symm.injective e))
  · filter_upwards [op.mem_nhds bu] with y hy
    ext x
    constructor
    · intro eqv
      have px : p x=y := eqv
      let a : p ⁻¹' U := ⟨x,show p x∈U from px.symm ▸ hy⟩
      let i := idx.symm (H a).2
      refine ⟨i,?_⟩
      change sheet i y=x
      rw [show sheet i y=(H.symm (⟨y,hy⟩,idx i)).1 from dite_eq_left hy]
      have pair : ((⟨y,hy⟩ : U),idx i)=H a := Prod.ext (Subtype.ext (px.symm.trans (hp a).symm)) (idx.apply_symm_apply _)
      rw [pair,H.symm_apply_apply]
    · rintro ⟨i,rfl⟩
      change p (sheet i y)=y
      rw [show sheet i y=(H.symm (⟨y,hy⟩,idx i)).1 from dite_eq_left hy,← hp,H.apply_symm_apply]

/-- In a closed surface transverse to a tube of uniformly bounded
height, every nonempty section over a connected base is locally an
exhaustive positive finite collection of sheets. -/
theorem bounded_transverse_tube_has_finite_sheets {B E : Type*} [TopologicalSpace B] [T2Space B]
    [PreconnectedSpace B] [TopologicalSpace E] {T : B × ℝ → E} (ct : Continuous T)
    {S : Set E} (closed : IsClosed S) {r s : ℝ} (gap : s<r)
    (bound : ∀ q∈spatialTubeSlice T S r, |q.2|≤s) (hit : (spatialTubeSlice T S r).Nonempty)
    (loc : IsLocalHomeomorph (fun q : spatialTubeSlice T S r => q.1.1)) :
    ∀ b : B, Nonempty (FiniteSheetGerms (fun q : spatialTubeSlice T S r => q.1.1) b) := by
  let _ : Nonempty (spatialTubeSlice T S r) := hit.to_subtype
  have prop := compact_height_slab_projection_proper ct closed gap bound
  exact finite_sheet_germs_of_proper_projection prop loc (proper_local_homeomorph_surjective prop loc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_height_slab_projection_proper
#print axioms TwoAxisHelicoid.bounded_transverse_tube_has_finite_sheets
