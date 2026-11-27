import TwoAxisHelicoid.ImmersionSpatialSpin
import TwoAxisHelicoid.TangentPlaneGramMembership
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Matrix

theorem tangentPairNormal_continuous : Continuous tangentPairNormal := by
  change Continuous (fun p : OrthonormalTangentPair => p.1.1 ⨯₃ p.1.2)
  simp only [cross_apply]
  fun_prop

theorem tangentPairNormal_ne_zero (p : OrthonormalTangentPair) : tangentPairNormal p ≠ 0 := by
  intro h
  have hd := tangentPairNormal_dot_self p
  rw [h,zero_dotProduct] at hd
  exact zero_ne_one hd

def spatialNormalKernel (n : Fin 3 → ℝ) : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v ⬝ᵥ n = 0}
  zero_mem' := zero_dotProduct n
  add_mem' := fun {a b} ha hb => by change (a+b) ⬝ᵥ n = 0; rw [add_dotProduct,ha,hb,add_zero]
  smul_mem' := fun r {a} ha => by change (r • a) ⬝ᵥ n = 0; rw [smul_dotProduct,ha,smul_zero]

/-- An actual regular spatial differential has its image in the plane
orthogonal to the normal constructed by Gram--Schmidt. -/
theorem spatial_differential_mem_normal_kernel {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hi : Function.Injective D) (v : ℂ) :
    D v ∈ spatialNormalKernel (tangentPairNormal (spatialDifferentialFrame hi (v := 1) one_ne_zero)) := by
  let p := spatialDifferentialFrame hi (v := 1) one_ne_zero
  let K := spatialNormalKernel (tangentPairNormal p)
  have hAB : p.1.1 ∈ K ∧ p.1.2 ∈ K := ⟨dot_self_cross _ _,dot_cross_self _ _⟩
  have hm := (spatialGramFrame_mem_iff K _ _).mp hAB
  simp only [mul_one] at hm
  have he : v = v.re • (1 : ℂ) + v.im • I := by
    simpa only [Complex.real_smul,mul_one] using (Complex.re_add_im v).symm
  have hD : D v = v.re • D 1 + v.im • D I := by conv_lhs => rw [he,map_add,map_smul,map_smul]
  rw [hD]
  exact K.add_mem (K.smul_mem _ hm.1) (K.smul_mem _ hm.2)

/-- Equality of real tangent planes determines the unit normal up to the
unique sign. This also applies when the two parameterizations have
different orientation. -/
theorem spatial_differential_normal_eq_or_neg {D E : ℂ →L[ℝ] (Fin 3 → ℝ)}
    (hi : Function.Injective D) (hj : Function.Injective E)
    (he : LinearMap.range E.toLinearMap ≤ LinearMap.range D.toLinearMap) :
    let n := tangentPairNormal (spatialDifferentialFrame hi (v := 1) one_ne_zero)
    let m := tangentPairNormal (spatialDifferentialFrame hj (v := 1) one_ne_zero)
    n = m ∨ n = -m := by
  let p := spatialDifferentialFrame hi (v := 1) one_ne_zero
  let q := spatialDifferentialFrame hj (v := 1) one_ne_zero
  let n := tangentPairNormal p
  let m := tangentPairNormal q
  let K := spatialNormalKernel n
  have hmem (v : ℂ) : E v ∈ K := by
    obtain ⟨w,hw⟩ := he (show E v ∈ LinearMap.range E.toLinearMap from ⟨v,rfl⟩)
    rw [← hw]
    exact spatial_differential_mem_normal_kernel hi w
  obtain ⟨ha,hb⟩ := (spatialGramFrame_mem_iff K _ _).mpr ⟨hmem 1,hmem (I*1)⟩
  change q.1.1 ⬝ᵥ n = 0 at ha
  change q.1.2 ⬝ᵥ n = 0 at hb
  have hcross : m ⨯₃ n = 0 := by
    change (q.1.1 ⨯₃ q.1.2) ⨯₃ n = 0
    rw [cross_cross_eq_smul_sub_smul,ha,hb,zero_smul,zero_smul,sub_zero]
  have hrel : n = (m ⬝ᵥ n) • m := by
    have H := cross_cross_eq_smul_sub_smul' m m n
    rw [hcross,map_zero,tangentPairNormal_dot_self q,one_smul] at H
    exact (sub_eq_zero.mp H.symm).symm
  have ha2 : (m ⬝ᵥ n)^2 = 1 := by
    have hh (c : ℝ) : (c • m) ⬝ᵥ (c • m) = c^2 := by
      rw [smul_dotProduct,dotProduct_smul,tangentPairNormal_dot_self q]
      simp [sq]
    exact (hh _).symm.trans (by rw [← hrel]; exact tangentPairNormal_dot_self p)
  rcases sq_eq_one_iff.mp ha2 with hs | hs
  · left
    simpa only [hs,one_smul] using hrel
  · right
    simpa only [hs,neg_one_smul] using hrel

theorem continuous_signed_normal_unique {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]
    (f g : C(S,Fin 3 → ℝ)) (hn : ∀ x, g x ≠ 0)
    (h : ∀ x, f x = g x ∨ f x = -g x) : (∀ x, f x = g x) ∨ ∀ x, f x = -g x := by
  let U := {x | f x = g x}
  have hU : IsClosed U := isClosed_eq f.continuous g.continuous
  have hUc : Uᶜ = {x | f x = -g x} := by
    ext x
    constructor
    · intro hx
      exact (h x).resolve_left hx
    · intro he he'
      apply hn x
      have hg : g x = -g x := he'.symm.trans he
      funext i
      have hh := congrFun hg i
      change g x i = -(g x i) at hh
      change g x i = 0
      linarith
  have hcc : IsClopen U := ⟨hU,by rw [← isClosed_compl_iff,hUc]; exact isClosed_eq f.continuous g.continuous.neg⟩
  rcases isClopen_iff.mp hcc with h0 | h1
  · right
    intro x
    apply (h x).resolve_left
    change x ∉ U
    rw [h0]
    exact notMem_empty _
  · left
    intro x
    change x ∈ U
    rw [h1]
    exact mem_univ _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_differential_normal_eq_or_neg
#print axioms TwoAxisHelicoid.continuous_signed_normal_unique
