import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- Logarithmic coordinates on a punctured disk, with the left half-plane
itself parameterized by a topological copy of the entire plane. -/
theorem punctured_disk_cyclic_plane_cover {R : ℝ} (hR : 0<R) :
    ∃ p : ℂ → {z : ℂ // 0<‖z‖ ∧ ‖z‖<R}, IsCoveringMap p ∧ Function.Surjective p ∧
      ∀ z w, p z=p w ↔ ∃ n : ℤ, z=w+(n:ℂ)*(2*(Real.pi:ℂ)*I) := by
  let f := fun z : ℂ => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {z : ℂ // z≠0})
  let T := {v : {z : ℂ // z≠0} | ‖v.1‖<R}
  let W := f ⁻¹' T
  let a := fun z : ℂ => ((Real.log R-Real.exp z.re : ℝ):ℂ)+(z.im:ℂ)*I
  have reA (z : ℂ) : (a z).re=Real.log R-Real.exp z.re := by
    change ((Real.log R-Real.exp z.re : ℝ):ℂ).re+((z.im:ℂ)*I).re=_
    rw [Complex.ofReal_re,Complex.mul_re]
    simp
  have imA (z : ℂ) : (a z).im=z.im := by simp [a]
  have region (w : ℂ) : w∈W ↔ w.re<Real.log R := by
    change ‖Complex.exp w‖<R ↔ _
    rw [Complex.norm_exp,Real.lt_log_iff_exp_lt hR]
  have memA (z : ℂ) : a z∈W := (region _).mpr (by rw [reA]; linarith [Real.exp_pos z.re])
  let inv := fun w : W => ((Real.log (Real.log R-w.1.re):ℝ):ℂ)+(w.1.im:ℂ)*I
  let e : ℂ ≃ₜ W :=
    { toFun := fun z => ⟨a z,memA z⟩
      invFun := inv
      left_inv := fun z => by
        apply Complex.ext
        · simp [inv,reA,Real.log_exp]
        · simp [inv,imA]
      right_inv := fun w => by
        apply Subtype.ext
        apply Complex.ext
        · rw [reA]
          simp [inv,Real.exp_log (sub_pos.mpr ((region _).mp w.2))]
        · simp [imA,inv]
      continuous_toFun := Continuous.subtype_mk (by dsimp [a]; fun_prop) _
      continuous_invFun := by
        have pos (w : W) : 0<Real.log R-w.1.re := sub_pos.mpr ((region _).mp w.2)
        dsimp [inv]
        fun_prop (disch := exact fun x => (pos x).ne') }
  let H : T ≃ₜ {z : ℂ // 0<‖z‖ ∧ ‖z‖<R} :=
    { toFun := fun q => ⟨q.1.1,norm_pos_iff.mpr q.1.2,q.2⟩
      invFun := fun w => ⟨⟨w.1,norm_pos_iff.mp w.2.1⟩,w.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let p := H ∘ (T.restrictPreimage f) ∘ e
  have cov : IsCoveringMap p := ((Complex.isCoveringMap_exp.restrictPreimage T).comp_homeomorph e).homeomorph_comp H
  have sur : Function.Surjective (T.restrictPreimage f) := by
    intro q
    let z := Complex.log q.1.1
    have eq : f z=q.1 := Subtype.ext (Complex.exp_log q.1.2)
    exact ⟨⟨z,show f z∈T from eq ▸ q.2⟩,Subtype.ext eq⟩
  refine ⟨p,cov,H.surjective.comp (sur.comp e.surjective),?_⟩
  have shift (w : ℂ) (n : ℤ) : a (w+(n:ℂ)*(2*(Real.pi:ℂ)*I))=a w+(n:ℂ)*(2*(Real.pi:ℂ)*I) := by
    apply Complex.ext <;> simp [reA,imA,Complex.mul_re,Complex.mul_im]
  intro z w
  have eq : p z=p w ↔ Complex.exp (a z)=Complex.exp (a w) := Subtype.ext_iff
  rw [eq,Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,h⟩
    exact ⟨n,e.injective (Subtype.ext (h.trans (shift w n).symm))⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,shift w n⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_disk_cyclic_plane_cover
