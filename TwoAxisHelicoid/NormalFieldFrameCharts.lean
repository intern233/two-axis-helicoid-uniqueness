import TwoAxisHelicoid.SpatialDifferentialNormal
import TwoAxisHelicoid.NormalFieldSpinCover

namespace TwoAxisHelicoid
open Set Topology Matrix
open scoped Matrix

variable {B : Type*} [TopologicalSpace B]

/-- Near any oriented orthonormal frame of a continuous unit-normal field, a
reference tangent frame is obtained by crossing the moving normal with the
fixed first vector of that frame. -/
theorem normal_field_local_reference (n : C(B,Fin 3 → ℝ)) (hn : ∀ b, n b ⬝ᵥ n b = 1)
    (x : NormalFieldFrames n) : ∃ (U : Set B), IsOpen U ∧ x.1.1 ∈ U ∧
      ∃ f : C(U,OrthonormalTangentPair), ∀ u, n u.1 = tangentPairNormal (f u) := by
  let v := x.1.2.1.1
  let T (b : B) := n b ⨯₃ v
  have hT : Continuous T := by
    change Continuous (fun b => n b ⨯₃ v)
    simp only [cross_apply]
    fun_prop
  let U := {b : B | T b ≠ 0}
  have hx : x.1.1 ∈ U := by
    intro h
    have hz : x.1.2.1.2 = 0 := by
      rw [← tangentPairNormal_cross_first]
      change tangentPairNormal x.1.2 ⨯₃ v = 0
      rw [← x.2]; exact h
    have hh := x.1.2.2.2.1
    rw [hz,zero_dotProduct] at hh
    exact zero_ne_one hh
  let A (u : U) := spatialUnitVector (T u.1)
  let C (u : U) := n u.1 ⨯₃ A u
  have hA (u : U) : A u ⬝ᵥ A u = 1 := spatialUnitVector_unit u.2
  have hN (u : U) : n u.1 ⬝ᵥ A u = 0 := by
    change n u.1 ⬝ᵥ spatialUnitVector (n u.1 ⨯₃ v) = 0
    rw [spatialUnitVector,dotProduct_smul,dot_self_cross,smul_zero]
  have hC (u : U) : C u ⬝ᵥ C u = 1 := by
    change (n u.1 ⨯₃ A u) ⬝ᵥ (n u.1 ⨯₃ A u) = 1
    rw [cross_dot_cross,hn,hA,hN,zero_mul,sub_zero,one_mul]
  have ha : Continuous A := spatialUnitVector_continuous (hT.comp continuous_subtype_val) fun u => u.2
  have hc : Continuous C := by
    change Continuous (fun u : U => n u.1 ⨯₃ A u)
    simp only [cross_apply]
    fun_prop
  let f : C(U,OrthonormalTangentPair) := ⟨fun u => ⟨(A u,C u),hA u,hC u,dot_cross_self _ _⟩,
    (ha.prodMk hc).subtype_mk _⟩
  refine ⟨U,isOpen_ne_fun hT continuous_const,hx,f,?_⟩
  intro u
  change n u.1 = A u ⨯₃ (n u.1 ⨯₃ A u)
  rw [cross_cross_eq_smul_sub_smul',hA,hN,one_smul,zero_smul,sub_zero]

/-- Local angular coordinates for all frames in the actual oriented planes,
including the plane at the compactifying point. The first coordinate is
literally the base point. -/
noncomputable def normalFrameChart {n : B → Fin 3 → ℝ} {U : Set B}
    (f : C(U,OrthonormalTangentPair)) (hn : ∀ u : U, n u.1 = tangentPairNormal (f u)) :
    {x : NormalFieldFrames n // x.1.1 ∈ U} ≃ₜ U × Circle := by
  let J : OrientedPlaneFrames f ≃ₜ {s : NormalFieldFrames n // s.1.1 ∈ U} := {
    toFun := fun s => ⟨⟨(s.1.1.1,s.1.2),(hn s.1.1).trans s.2⟩,s.1.1.2⟩
    invFun := fun x => ⟨(⟨x.1.1.1,x.2⟩,x.1.1.2),(hn ⟨x.1.1.1,x.2⟩).symm.trans x.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      have h := continuous_subtype_val (p := fun v : U × OrthonormalTangentPair =>
        tangentPairNormal (f v.1) = tangentPairNormal v.2)
      exact ((((continuous_subtype_val.comp h.fst).prodMk h.snd).subtype_mk _).subtype_mk _)
    continuous_invFun := by
      have h := continuous_subtype_val.comp (continuous_subtype_val (p := fun v : NormalFieldFrames n => v.1.1 ∈ U))
      exact ((h.fst.subtype_mk _).prodMk h.snd).subtype_mk _ }
  exact J.symm.trans (orientedPlaneFrameHomeomorph f f.continuous).symm

theorem normalFrameChart_base {n : B → Fin 3 → ℝ} {U : Set B} (f : C(U,OrthonormalTangentPair))
    (hn : ∀ u : U, n u.1 = tangentPairNormal (f u)) (x : {s : NormalFieldFrames n // s.1.1 ∈ U}) :
    ((normalFrameChart f hn x).1 : B) = x.1.1.1 := rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normal_field_local_reference
#print axioms TwoAxisHelicoid.normalFrameChart
