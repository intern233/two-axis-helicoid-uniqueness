import TwoAxisHelicoid.NormalFiberHomeomorph

namespace TwoAxisHelicoid
open Set

noncomputable def fiberClampedTime (time : ℝ) : ℝ := max 0 (min 1 time)

theorem fiberClampedTime_mem (time : ℝ) : fiberClampedTime time ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem fiberClampedTime_of_mem {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    fiberClampedTime time = time := by
  rw [fiberClampedTime,min_eq_right htime.2,max_eq_right htime.1]

theorem fiberClampedTime_continuous : Continuous fiberClampedTime := by
  unfold fiberClampedTime
  fun_prop

variable {P : Type*} [NormedAddCommGroup P] [ProperSpace P]
  {χ : ℝ → ℝ} {C R U : ℝ} (hχ : FiberCutoff χ C R) {u : P → ℝ}
  (huc : Continuous u) (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1)

@[simp] theorem normalFiberHomeomorph_apply {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (x : ℝ × P) : normalFiberHomeomorph hχ huc hu hsmall htime x = normalFiberShift χ u time x := rfl

/-- One homeomorphism also including the time parameter. Its inverse
will give joint continuity of the inverses of the individual time slices. -/
noncomputable def normalFiberJointHomeomorph : (ℝ × (ℝ × P)) ≃ₜ (ℝ × (ℝ × P)) :=
  normalFiberHomeomorph hχ
    (u := fun q : ℝ × P => fiberClampedTime q.1*u q.2)
    ((fiberClampedTime_continuous.comp continuous_fst).mul (huc.comp continuous_snd))
    (fun q => by
      rw [abs_mul,abs_of_nonneg (fiberClampedTime_mem q.1).1]
      exact (mul_le_mul_of_nonneg_right (fiberClampedTime_mem q.1).2 (abs_nonneg _)).trans
        (by simpa only [one_mul] using hu q.2))
    hsmall (by norm_num : (1 : ℝ) ∈ Icc 0 1)

theorem normalFiberJointHomeomorph_apply (s time : ℝ) (p : P) :
    normalFiberJointHomeomorph hχ huc hu hsmall (s,(time,p)) =
      (scalarFiberShift χ (fiberClampedTime time*u p) s,(time,p)) := by
  change (scalarFiberShift χ (1*(fiberClampedTime time*u p)) s,(time,p)) = _
  rw [one_mul]

theorem normalFiberHomeomorph_inverse_slice {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (s : ℝ) (p : P) :
    (normalFiberHomeomorph hχ huc hu hsmall htime).symm (s,p) =
      (((normalFiberJointHomeomorph hχ huc hu hsmall).symm (s,(time,p))).1,p) := by
  let G := normalFiberJointHomeomorph hχ huc hu hsmall
  let y : ℝ × (ℝ × P) := (s,(time,p))
  have hb := G.apply_symm_apply y
  have hbase : (G.symm y).2 = (time,p) := congrArg Prod.snd hb
  have hf := congrArg Prod.fst hb
  change scalarFiberShift χ (1*(fiberClampedTime (G.symm y).2.1*u (G.symm y).2.2)) (G.symm y).1 = s at hf
  rw [hbase,fiberClampedTime_of_mem htime,one_mul] at hf
  apply (normalFiberHomeomorph hχ huc hu hsmall htime).injective
  rw [Homeomorph.apply_symm_apply,normalFiberHomeomorph_apply]
  exact Prod.ext hf.symm rfl

theorem normalFiberHomeomorph_joint_continuous :
    Continuous (fun q : Icc (0 : ℝ) 1 × (ℝ × P) =>
      normalFiberHomeomorph hχ huc hu hsmall q.1.2 q.2) := by
  change Continuous (fun q : Icc (0 : ℝ) 1 × (ℝ × P) =>
    (q.2.1+χ q.2.1*(q.1.1*u q.2.2),q.2.2))
  have hc := hχ.differentiable.continuous
  fun_prop

theorem normalFiberHomeomorph_inverse_joint_continuous :
    Continuous (fun q : Icc (0 : ℝ) 1 × (ℝ × P) =>
      (normalFiberHomeomorph hχ huc hu hsmall q.1.2).symm q.2) := by
  have hc : Continuous (fun q : Icc (0 : ℝ) 1 × (ℝ × P) =>
      (((normalFiberJointHomeomorph hχ huc hu hsmall).symm (q.2.1,(q.1.1,q.2.2))).1,q.2.2)) := by
    fun_prop
  apply hc.congr
  intro q
  exact (normalFiberHomeomorph_inverse_slice hχ huc hu hsmall q.1.2 q.2.1 q.2.2).symm

theorem normalFiberHomeomorph_time_zero :
    normalFiberHomeomorph hχ huc hu hsmall (by norm_num : (0 : ℝ) ∈ Icc 0 1) =
      Homeomorph.refl (ℝ × P) := by
  apply Homeomorph.ext
  intro x
  change (x.1+χ x.1*(0*u x.2),x.2) = x
  simp only [zero_mul,mul_zero,add_zero,Prod.mk.eta]

theorem normalFiberHomeomorph_outside {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {x : ℝ × P} (hx : R ≤ |x.1|) : normalFiberHomeomorph hχ huc hu hsmall htime x = x := by
  apply Prod.ext
  · exact scalarFiberShift_eq_self hχ.support_bound hx
  · rfl

theorem normalFiberHomeomorph_fixes_zero_height {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    {p : P} (hp : u p = 0) (s : ℝ) : normalFiberHomeomorph hχ huc hu hsmall htime (s,p) = (s,p) := by
  simp only [normalFiberHomeomorph_apply,normalFiberShift,scalarFiberShift,hp,mul_zero,add_zero]

theorem normalFiberHomeomorph_time_one_graph (p : P) :
    normalFiberHomeomorph hχ huc hu hsmall (by norm_num : (1 : ℝ) ∈ Icc 0 1) (0,p) = (u p,p) := by
  change (scalarFiberShift χ (1*u p) 0,p) = _
  rw [one_mul,scalarFiberShift_zero χ (u p) hχ.at_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalFiberHomeomorph_inverse_joint_continuous
#print axioms TwoAxisHelicoid.normalFiberHomeomorph_time_one_graph
