import TwoAxisHelicoid.ImmersedDiskBoundarySpin

namespace TwoAxisHelicoid
open Set Matrix
open scoped Matrix

/-- Convex interpolation of two unit spatial vectors vanishes only for
antipodal endpoints. -/
theorem unit_spatial_segment_ne_zero {u v : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (hanti : v ≠ -u) (s : unitInterval) : (1-s.1) • u+s.1 • v ≠ 0 := by
  intro h
  have he : (1-s.1) • u = -(s.1 • v) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg (fun w : Fin 3 → ℝ => w ⬝ᵥ w) he
  simp only [neg_dotProduct,dotProduct_neg,smul_dotProduct,dotProduct_smul,hu,hv,
    smul_eq_mul,mul_one] at hn
  have heq : 1-s.1 = s.1 := by nlinarith
  have hs : s.1 ≠ 0 := by linarith
  apply hanti
  apply funext
  intro i
  have hi := congrFun he i
  change (1-s.1)*u i = -(s.1*v i) at hi
  rw [heq,← mul_neg] at hi
  change v i = -u i
  exact (neg_eq_iff_eq_neg.mp (mul_left_cancel₀ hs hi).symm)

/-- Keeping the common first tangent and rotating the positive transverse
unit vector through the short arc gives a free homotopy of closed spatial
frames along a transverse meeting of two surfaces. -/
theorem common_tangent_frame_closed_lift {p r : C(unitInterval,OrthonormalTangentPair)}
    (hp : p 1 = p 0) (hr : r 1 = r 0)
    (hfirst : ∀ t, (p t).1.1 = (r t).1.1) (hanti : ∀ t, (r t).1.2 ≠ -(p t).1.2)
    (q : C(unitInterval,UnitQuaternion)) (hq : ∀ t, unitQuaternionFrame (q t) = p t)
    (hc : q 1 = q 0) :
    ∃ l : C(unitInterval,UnitQuaternion), (∀ t, unitQuaternionFrame (l t) = r t) ∧ l 1 = l 0 := by
  let V := fun z : unitInterval × unitInterval => (1-z.1.1) • (p z.2).1.2+z.1.1 • (r z.2).1.2
  have hn (z) : V z ≠ 0 := unit_spatial_segment_ne_zero (p z.2).2.2.1 (r z.2).2.2.1 (hanti z.2) z.1
  have hpV (z) : (p z.2).1.1 ⬝ᵥ V z = 0 := by
    have hh : (p z.2).1.1 ⬝ᵥ (r z.2).1.2 = 0 := hfirst z.2 ▸ (r z.2).2.2.2
    simp [V,dotProduct_add,dotProduct_smul,hh,(p z.2).2.2.2]
  let B (z : unitInterval × unitInterval) : OrthonormalTangentPair :=
    ⟨((p z.2).1.1,spatialUnitVector (V z)),(p z.2).2.1,spatialUnitVector_unit (hn z),
      by simp [spatialUnitVector,dotProduct_smul,hpV z]⟩
  have hpc := continuous_subtype_val.comp (p.continuous.comp (continuous_snd (X := unitInterval)))
  have hrc := continuous_subtype_val.comp (r.continuous.comp (continuous_snd (X := unitInterval)))
  have hs := continuous_subtype_val.comp (continuous_fst (Y := unitInterval) (X := unitInterval))
  have hv : Continuous V := ((continuous_const.sub hs).smul hpc.snd).add (hs.smul hrc.snd)
  let H : C(unitInterval × unitInterval,OrthonormalTangentPair) :=
    ⟨B,(hpc.fst.prodMk (spatialUnitVector_continuous hv hn)).subtype_mk _⟩
  have unitVec {w : Fin 3 → ℝ} (hw : w ⬝ᵥ w = 1) : spatialUnitVector w = w := by
    simpa using spatialUnitVector_eq_of_normalized (k := 1) zero_lt_one (by simpa using hw)
  have hends (s : unitInterval) : H (s,1) = H (s,0) := by
    apply Subtype.ext
    simp only [H,ContinuousMap.coe_mk,B,V,hp,hr]
  have h0 (t) : H (0,t) = p t := by
    apply Subtype.ext
    simp [H,B,V,unitVec (p t).2.2.1]
  have h1 (t) : H (1,t) = r t := by
    apply Subtype.ext
    simp [H,B,V,unitVec (r t).2.2.1,hfirst]
  obtain ⟨l,hl,he⟩ := quaternion_loop_closed_lift_homotopy H hends q (fun t => (hq t).trans (h0 t).symm) hc
  exact ⟨l,fun t => (hl t).trans (h1 t),he⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.common_tangent_frame_closed_lift
