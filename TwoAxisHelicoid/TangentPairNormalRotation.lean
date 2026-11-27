import TwoAxisHelicoid.SpinCircleAction

namespace TwoAxisHelicoid
open Complex Matrix
open scoped Matrix

def tangentPairNormal (p : OrthonormalTangentPair) : Fin 3 → ℝ :=
  p.1.1 ⨯₃ p.1.2

theorem tangentPairNormal_cross_first (p : OrthonormalTangentPair) :
    tangentPairNormal p ⨯₃ p.1.1 = p.1.2 := by
  rw [tangentPairNormal,cross_cross_eq_smul_sub_smul,dotProduct_comm p.1.2,
    p.2.1,p.2.2.2,one_smul,zero_smul,sub_zero]

theorem tangentPairNormal_cross_second (p : OrthonormalTangentPair) :
    tangentPairNormal p ⨯₃ p.1.2 = -p.1.1 := by
  rw [tangentPairNormal,cross_cross_eq_smul_sub_smul,p.2.2.2,p.2.2.1,zero_smul,one_smul,zero_sub]

theorem rotateTangentPair_same_normal (u : Circle) (p : OrthonormalTangentPair) :
    tangentPairNormal (rotateTangentPair u p) = tangentPairNormal p := by
  let A := p.1.1
  let B := p.1.2
  let r := (u : ℂ).re
  let s := (u : ℂ).im
  have hu : r*r+s*s = 1 := u.normSq_coe
  change (r • A+s • B) ⨯₃ ((-s) • A+r • B) = A ⨯₃ B
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,cross_self,smul_zero,
    zero_add,add_zero,← cross_anticomm A B]
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  linear_combination (A ⨯₃ B) i * hu

/-- The inverse circle coordinate of an oriented orthonormal frame in
the same tangent plane is recovered by actual Euclidean dot products. -/
def tangentPairPhase (p q : OrthonormalTangentPair) : ℂ :=
  ⟨p.1.1 ⬝ᵥ q.1.1,p.1.2 ⬝ᵥ q.1.1⟩

theorem tangentPairPhase_rotate (p : OrthonormalTangentPair) (u : Circle) :
    tangentPairPhase p (rotateTangentPair u p) = (u : ℂ) := by
  apply Complex.ext
  · change p.1.1 ⬝ᵥ ((u : ℂ).re • p.1.1+(u : ℂ).im • p.1.2) = _
    simp [dotProduct_add,p.2.1,p.2.2.2]
  · change p.1.2 ⬝ᵥ ((u : ℂ).re • p.1.1+(u : ℂ).im • p.1.2) = _
    have hBA : p.1.2 ⬝ᵥ p.1.1 = 0 := (dotProduct_comm _ _).trans p.2.2.2
    simp [dotProduct_add,p.2.2.1,hBA]

theorem tangentPair_same_normal_rotate (p q : OrthonormalTangentPair)
    (hn : tangentPairNormal p = tangentPairNormal q) :
    ∃ u : Circle, rotateTangentPair u p = q := by
  let r := p.1.1 ⬝ᵥ q.1.1
  let s := p.1.2 ⬝ᵥ q.1.1
  have hD : q.1.2 = r • p.1.2 - s • p.1.1 := calc
    q.1.2 = tangentPairNormal q ⨯₃ q.1.1 := (tangentPairNormal_cross_first q).symm
    _ = tangentPairNormal p ⨯₃ q.1.1 := by rw [hn]
    _ = _ := cross_cross_eq_smul_sub_smul _ _ _
  have hC : q.1.1 = r • p.1.1+s • p.1.2 := by
    have h := tangentPairNormal_cross_second q
    rw [← hn,hD,map_sub,map_smul,map_smul,tangentPairNormal_cross_second,
      tangentPairNormal_cross_first] at h
    rw [← neg_inj]
    rw [← h]
    module
  have hrs : r*r+s*s = 1 := calc
    _ = q.1.1 ⬝ᵥ (r • p.1.1+s • p.1.2) := by
      rw [dotProduct_add,dotProduct_smul,dotProduct_smul,smul_eq_mul,smul_eq_mul,
        dotProduct_comm q.1.1 p.1.1,dotProduct_comm q.1.1 p.1.2]
    _ = 1 := by rw [← hC,q.2.1]
  let u : Circle := ⟨⟨r,s⟩,mem_sphere_zero_iff_norm.mpr (by
    have hns : Complex.normSq ⟨r,s⟩ = 1 := hrs
    rw [Complex.norm_def,hns,Real.sqrt_one])⟩
  refine ⟨u,Subtype.ext (Prod.ext hC.symm ?_)⟩
  change (-s) • p.1.1+r • p.1.2 = q.1.2
  rw [hD]
  module

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.tangentPair_same_normal_rotate
