import TwoAxisHelicoid.SpatialQuaternionAction

namespace TwoAxisHelicoid
open Matrix
open scoped Matrix Quaternion

private def spatialFirst : Fin 3 → ℝ := ![1,0,0]
private def spatialSecond : Fin 3 → ℝ := ![0,1,0]
private def spatialThird : Fin 3 → ℝ := ![0,0,1]

private theorem spatial_expand (v : Fin 3 → ℝ) : v=v 0 • spatialFirst+v 1 • spatialSecond+v 2 • spatialThird := by
  funext j
  fin_cases j <;> simp [spatialFirst,spatialSecond,spatialThird]

/-- Every orthogonal change of three-dimensional coordinates is a
quaternion rotation with a possible central inversion. -/
theorem orthogonal_has_signed_quaternion (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (ortho : ∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) :
    (∃ q : UnitQuaternion, ∀ v, spatialQuaternionAction q v=T v) ∨
    (∃ q : UnitQuaternion, ∀ v, spatialQuaternionAction q v= -T v) := by
  let A := T spatialFirst
  let B := T spatialSecond
  have dot1 : A ⬝ᵥ A=1 := (ortho _ _).trans (by simp [spatialFirst])
  have dot2 : B ⬝ᵥ B=1 := (ortho _ _).trans (by simp [spatialSecond])
  have perp : A ⬝ᵥ B=0 := (ortho _ _).trans (by simp [spatialFirst,spatialSecond])
  let frame : OrthonormalTangentPair := ⟨(A,B),dot1,dot2,perp⟩
  obtain ⟨q,hq⟩ := unitQuaternionFrame_surjective frame
  let N := A ⨯₃ B
  let V := T.symm N
  have n1 : N ⬝ᵥ N=1 := by rw [show N=A ⨯₃ B from rfl,cross_dot_cross,dot1,dot2,perp]; norm_num
  have back : T V=N := T.apply_symm_apply _
  have hx : V 0=0 := calc
    _ = spatialFirst ⬝ᵥ V := by simp [spatialFirst,dotProduct,Fin.sum_univ_three]
    _ = A ⬝ᵥ N := by rw [← back]; exact (ortho _ _).symm
    _ = _ := dot_self_cross _ _
  have hy : V 1=0 := calc
    _ = spatialSecond ⬝ᵥ V := by simp [spatialSecond,dotProduct,Fin.sum_univ_three]
    _ = B ⬝ᵥ N := by rw [← back]; exact (ortho _ _).symm
    _ = _ := dot_cross_self _ _
  have norm : V ⬝ᵥ V=1 := (ortho V V).symm.trans (back ▸ n1)
  have vsq : (V 2)^2=1 := by simpa [dotProduct,Fin.sum_univ_three,hx,hy,pow_two] using norm
  have columns (v) : spatialQuaternionAction q v=v 0 • A+v 1 • B+v 2 • N := by rw [spatialQuaternionAction_columns,hq]; rfl
  have linear (v) : T v=v 0 • A+v 1 • B+v 2 • T spatialThird := by
    calc
      T v = T (v 0 • spatialFirst+v 1 • spatialSecond+v 2 • spatialThird) := congrArg T (spatial_expand v)
      _ = _ := by simp [A,B]
  rcases sq_eq_one_iff.mp vsq with plus | minus
  · left
    have e : V=spatialThird := by funext j; fin_cases j <;> simp [spatialThird,hx,hy,plus]
    exact ⟨q,fun v => (columns v).trans (by rw [← back,e]; exact (linear v).symm)⟩
  · right
    have e : V= -spatialThird := by funext j; fin_cases j <;> simp [spatialThird,hx,hy,minus]
    have n : N= -T spatialThird := by rw [← back,e,map_neg]
    refine ⟨unitQuaternionCompose q unitQuaternionK,fun v => ?_⟩
    rw [spatialQuaternionAction_compose,spatialQuaternionAction_K,columns,linear v,n]
    simp [add_comm]

/-- Both components of the ambient orthogonal group lift continuously
on adapted tangent frames. For orientation reversal the fixed right
half-turn reverses both tangent axes of the lifted quaternion. -/
theorem orthogonal_tangent_pair_quaternion_lift (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (ortho : ∀ v w, T v ⬝ᵥ T w=v ⬝ᵥ w) :
    ∃ H : C(UnitQuaternion,UnitQuaternion), ∀ u,
      (unitQuaternionFrame (H u)).1=(T (unitQuaternionFrame u).1.1,T (unitQuaternionFrame u).1.2) := by
  have left (p : UnitQuaternion) : Continuous (unitQuaternionCompose p) :=
    continuous_unitQuaternionCompose.comp (continuous_const.prodMk continuous_id)
  have right : Continuous (fun u => unitQuaternionCompose u unitQuaternionK) :=
    continuous_unitQuaternionCompose.comp (continuous_id.prodMk continuous_const)
  rcases orthogonal_has_signed_quaternion T ortho with ⟨p,hp⟩ | ⟨p,hp⟩
  · refine ⟨⟨_,left p⟩,fun u => ?_⟩
    apply Prod.ext
    · exact ((spatialQuaternionAction_axes _).1.symm.trans (spatialQuaternionAction_compose p u _)).trans
        ((hp _).trans (congrArg T (spatialQuaternionAction_axes u).1))
    · exact ((spatialQuaternionAction_axes _).2.1.symm.trans (spatialQuaternionAction_compose p u _)).trans
        ((hp _).trans (congrArg T (spatialQuaternionAction_axes u).2.1))
  · let H := fun u => unitQuaternionCompose (unitQuaternionCompose p u) unitQuaternionK
    refine ⟨⟨H,right.comp (left p)⟩,fun u => ?_⟩
    have first : spatialQuaternionAction unitQuaternionK spatialFirst= -spatialFirst := by rw [spatialQuaternionAction_K]; ext j; fin_cases j <;> norm_num [spatialFirst]
    have second : spatialQuaternionAction unitQuaternionK spatialSecond= -spatialSecond := by rw [spatialQuaternionAction_K]; ext j; fin_cases j <;> norm_num [spatialSecond]
    have eval {v : Fin 3 → ℝ} (negative : spatialQuaternionAction unitQuaternionK v= -v) :
        spatialQuaternionAction (H u) v=T (spatialQuaternionAction u v) := by
      change spatialQuaternionAction (unitQuaternionCompose (unitQuaternionCompose p u) unitQuaternionK) v=_
      rw [spatialQuaternionAction_compose,negative,spatialQuaternionAction_neg,spatialQuaternionAction_compose,hp,neg_neg]
    exact Prod.ext ((spatialQuaternionAction_axes _).1.symm.trans ((eval first).trans (congrArg T (spatialQuaternionAction_axes u).1)))
      ((spatialQuaternionAction_axes _).2.1.symm.trans ((eval second).trans (congrArg T (spatialQuaternionAction_axes u).2.1)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orthogonal_has_signed_quaternion
#print axioms TwoAxisHelicoid.orthogonal_tangent_pair_quaternion_lift
