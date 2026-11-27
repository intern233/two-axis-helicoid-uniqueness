import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Homotopy.Path

namespace TwoAxisHelicoid
open Set Filter Metric Function Topology
open scoped Topology ContDiff

/-- Smooth a based loop inside an arbitrary open ambient neighborhood.
The support control in smooth approximation fixes the entire constant
part of its extension, hence both endpoints throughout the homotopy. -/
theorem smooth_based_loop_in_open_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set E} (op : IsOpen O) {b : O} (γ : Path b b) :
    ∃ (g : ℝ → O) (c : Path b b), Continuous g ∧ ContDiff ℝ 1 (Subtype.val ∘ g) ∧
      (∀ t : unitInterval, c t=g t) ∧ γ.Homotopic c := by
  let α := γ.map continuous_subtype_val
  let K := range α
  have compK : IsCompact K := isCompact_range α.continuous
  have sub : K⊆O := by rintro _ ⟨t,rfl⟩; exact (γ t).2
  obtain ⟨δ,dp,safe⟩ := compK.exists_thickening_subset_open op sub
  let f := fun t : ℝ => α.extend t-b.1
  obtain ⟨a,sa,near,supp⟩ := Continuous.exists_contDiff_approx 1
    (show Continuous f from α.continuous_extend.sub continuous_const) (continuous_const (y := δ)) (fun _ => dp)
  let A := fun t => a t+b.1
  have smooth : ContDiff ℝ 1 A := sa.add contDiff_const
  have close (t : ℝ) : dist (A t) (α.extend t)<δ := by
    simpa only [A,f,dist_eq_norm,show a t+b.1-α.extend t=a t-(α.extend t-b.1) by abel] using near t
  have kept (t : ℝ) (eq : α.extend t=b.1) : A t=b.1 := by
    have zero : a t=0 := by
      by_contra nz
      have h := supp (show t∈support a from nz)
      exact h (sub_eq_zero.mpr eq)
    simp only [A,zero,zero_add]
  have contained (t : ℝ) (y : E) (hy : dist y (α.extend t)<δ) : y∈O :=
    safe (mem_thickening_iff.mpr ⟨α.extend t,by change α.extend t∈range α; rw [← α.extend_range]; exact mem_range_self t,hy⟩)
  let g := fun t => (⟨A t,contained t _ (close t)⟩ : O)
  have cg : Continuous g := smooth.continuous.subtype_mk _
  have g0 : g 0=b := Subtype.ext (kept 0 (α.extend_of_le_zero le_rfl))
  have g1 : g 1=b := Subtype.ext (kept 1 (α.extend_of_one_le le_rfl))
  let c : Path b b := ⟨⟨fun t => g t,cg.comp continuous_subtype_val⟩,g0,g1⟩
  let H := fun u : unitInterval × unitInterval => (γ u.2).1 + (u.1:ℝ) • (A u.2-(γ u.2).1)
  have cH : Continuous H := ((continuous_subtype_val.comp γ.continuous).comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul (((smooth.continuous.comp continuous_subtype_val).comp continuous_snd).sub
      ((continuous_subtype_val.comp γ.continuous).comp continuous_snd)))
  have inside (u : unitInterval × unitInterval) : H u∈O := by
    apply contained u.2
    have target : α.extend (u.2:ℝ)=(γ u.2).1 := α.extend_extends' u.2
    rw [target,dist_eq_norm,show H u-(γ u.2).1=(u.1:ℝ) • (A u.2-(γ u.2).1) by dsimp [H]; abel,
      norm_smul,Real.norm_of_nonneg u.1.2.1]
    have bound := mul_le_mul_of_nonneg_right u.1.2.2 (norm_nonneg (A u.2-(γ u.2).1))
    rw [one_mul] at bound
    apply bound.trans_lt
    simpa only [target,dist_eq_norm] using close u.2
  refine ⟨g,c,cg,smooth,fun _ => rfl,⟨{
    toFun := fun u => ⟨H u,inside u⟩
    continuous_toFun := cH.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by simp [H])
    map_one_left := fun t => Subtype.ext (by simp [H,c,g])
    prop' := ?_ }⟩⟩
  intro t u hu
  rcases hu with h|h
  · subst u
    apply Subtype.ext
    change (γ 0).1+(t:ℝ) • (A 0-(γ 0).1)=(γ 0).1
    rw [γ.source,show A 0=b.1 from congrArg Subtype.val g0,sub_self,smul_zero,add_zero]
  · have h1 : u=1 := h
    subst u
    apply Subtype.ext
    change (γ 1).1+(t:ℝ) • (A 1-(γ 1).1)=(γ 1).1
    rw [γ.target,show A 1=b.1 from congrArg Subtype.val g1,sub_self,smul_zero,add_zero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_based_loop_in_open_space
