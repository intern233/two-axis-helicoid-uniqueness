import TwoAxisHelicoid.QuaternionTangentStabilizer

namespace TwoAxisHelicoid
open Matrix
open scoped Quaternion Matrix

def pureSpatialQuaternion (v : Fin 3 → ℝ) : ℍ := ⟨0,v 0,v 1,v 2⟩

noncomputable def unitQuaternionCompose (p q : UnitQuaternion) : UnitQuaternion :=
  ⟨p.1*q.1,by rw [map_mul,p.2,q.2,mul_one]⟩

theorem continuous_unitQuaternionCompose : Continuous (fun pq : UnitQuaternion × UnitQuaternion => unitQuaternionCompose pq.1 pq.2) :=
  ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The rotation obtained by conjugating pure imaginary quaternions,
written in the ordinary spatial coordinates used for the immersion. -/
noncomputable def spatialQuaternionAction (q : UnitQuaternion) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  quaternionImaginaryVector (q.1*pureSpatialQuaternion v*star q.1)

theorem pureSpatialQuaternion_conjugate (q : UnitQuaternion) (v : Fin 3 → ℝ) :
    pureSpatialQuaternion (spatialQuaternionAction q v)=q.1*pureSpatialQuaternion v*star q.1 := by
  apply Quaternion.ext
  · change 0=_
    simp [pureSpatialQuaternion]
    ring
  · rfl
  · rfl
  · rfl

theorem spatialQuaternionAction_compose (p q : UnitQuaternion) (v : Fin 3 → ℝ) :
    spatialQuaternionAction (unitQuaternionCompose p q) v=spatialQuaternionAction p (spatialQuaternionAction q v) := by
  change quaternionImaginaryVector ((p.1*q.1)*pureSpatialQuaternion v*star (p.1*q.1))=
    quaternionImaginaryVector (p.1*pureSpatialQuaternion (spatialQuaternionAction q v)*star p.1)
  rw [pureSpatialQuaternion_conjugate,star_mul]
  simp only [mul_assoc]

theorem spatialQuaternionAction_neg (q : UnitQuaternion) (v : Fin 3 → ℝ) :
    spatialQuaternionAction q (-v)= -spatialQuaternionAction q v := by
  have e : pureSpatialQuaternion (-v)= -pureSpatialQuaternion v := by ext <;> simp [pureSpatialQuaternion]
  unfold spatialQuaternionAction
  rw [e,mul_neg,neg_mul]
  funext j
  fin_cases j <;> rfl

theorem spatialQuaternionAction_columns (q : UnitQuaternion) (v : Fin 3 → ℝ) :
    spatialQuaternionAction q v =
      v 0 • (unitQuaternionFrame q).1.1+v 1 • (unitQuaternionFrame q).1.2+v 2 • tangentPairNormal (unitQuaternionFrame q) := by
  rw [unitQuaternionFrame_axisI,unitQuaternionFrame_axisJ,unitQuaternionFrame_normal_axisK]
  funext j
  fin_cases j <;> simp [spatialQuaternionAction,quaternionImaginaryVector,pureSpatialQuaternion,
    quaternionAxisI,quaternionAxisJ,quaternionAxisK] <;> ring

theorem spatialQuaternionAction_axes (q : UnitQuaternion) :
    spatialQuaternionAction q ![1,0,0]=(unitQuaternionFrame q).1.1 ∧
    spatialQuaternionAction q ![0,1,0]=(unitQuaternionFrame q).1.2 ∧
    spatialQuaternionAction q ![0,0,1]=tangentPairNormal (unitQuaternionFrame q) := by
  simp [spatialQuaternionAction_columns]

def unitQuaternionK : UnitQuaternion := ⟨quaternionAxisK,by norm_num [quaternionAxisK,Quaternion.normSq_def']⟩

theorem spatialQuaternionAction_K (v : Fin 3 → ℝ) :
    spatialQuaternionAction unitQuaternionK v= ![-v 0,-v 1,v 2] := by
  funext j
  fin_cases j <;> simp [spatialQuaternionAction,unitQuaternionK,quaternionImaginaryVector,pureSpatialQuaternion,quaternionAxisK]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialQuaternionAction_compose
#print axioms TwoAxisHelicoid.spatialQuaternionAction_columns
