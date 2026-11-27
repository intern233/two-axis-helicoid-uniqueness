import TwoAxisHelicoid.HelicoidNormalGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology

/-- The ordinary squared Euclidean distance to the parametrized helicoid. -/
noncomputable def helicoidSquaredDistance (p : ℝ × ℝ × ℝ) (r θ : ℝ) : ℝ :=
  (p.1-r*cos θ)^2+(p.2.1-r*sin θ)^2+(p.2.2-θ)^2

noncomputable def helicoidReducedDistance (p : ℝ × ℝ × ℝ) (θ : ℝ) : ℝ :=
  (p.1*sin θ-p.2.1*cos θ)^2+(p.2.2-θ)^2

theorem helicoidSquaredDistance_reduced (p : ℝ × ℝ × ℝ) (r θ : ℝ) :
    helicoidSquaredDistance p r θ =
      (r-(p.1*cos θ+p.2.1*sin θ))^2+helicoidReducedDistance p θ := by
  unfold helicoidSquaredDistance helicoidReducedDistance
  linear_combination (r^2-p.1^2-p.2.1^2)*(sin_sq_add_cos_sq θ)

theorem helicoidReducedDistance_exists_min (p : ℝ × ℝ × ℝ) :
    ∃ θ : ℝ, ∀ φ : ℝ, helicoidReducedDistance p θ ≤ helicoidReducedDistance p φ := by
  let M := |p.1|+|p.2.1|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hmid : p.2.2 ∈ Icc (p.2.2-M) (p.2.2+M) := ⟨by linarith,by linarith⟩
  have hc : Continuous (helicoidReducedDistance p) := by
    unfold helicoidReducedDistance
    fun_prop
  obtain ⟨θ,hθ,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨p.2.2,hmid⟩ hc.continuousOn
  refine ⟨θ,fun φ => ?_⟩
  by_cases hφ : φ ∈ Icc (p.2.2-M) (p.2.2+M)
  · exact hmin hφ
  · have hb : |p.1*sin p.2.2-p.2.1*cos p.2.2| ≤ |p.1|+|p.2.1| := by
      calc
        _ ≤ |p.1*sin p.2.2|+|p.2.1*cos p.2.2| := by
          simpa using abs_sub_le (p.1*sin p.2.2) 0 (p.2.1*cos p.2.2)
        _ = |p.1| * |sin p.2.2|+|p.2.1| * |cos p.2.2| := by rw [abs_mul,abs_mul]
        _ ≤ _ := by nlinarith [abs_sin_le_one p.2.2,abs_cos_le_one p.2.2,
          abs_nonneg p.1,abs_nonneg p.2.1]
    have hbase : helicoidReducedDistance p p.2.2 ≤ M^2 := by
      unfold helicoidReducedDistance
      have hs := (sq_le_sq₀ (abs_nonneg (p.1*sin p.2.2-p.2.1*cos p.2.2))
        (by positivity : 0 ≤ |p.1|+|p.2.1|)).mpr hb
      rw [sq_abs] at hs
      dsimp [M]
      nlinarith [abs_nonneg p.1,abs_nonneg p.2.1]
    have hfar : M^2 ≤ (p.2.2-φ)^2 := by
      simp only [mem_Icc,not_and_or,not_le] at hφ
      rcases hφ with hφ | hφ <;> nlinarith
    exact (hmin hmid).trans (hbase.trans (by
      unfold helicoidReducedDistance
      nlinarith [sq_nonneg (p.1*sin φ-p.2.1*cos φ)]))

theorem helicoidSquaredDistance_exists_min (p : ℝ × ℝ × ℝ) :
    ∃ r θ : ℝ, ∀ u φ : ℝ, helicoidSquaredDistance p r θ ≤ helicoidSquaredDistance p u φ := by
  obtain ⟨θ,hθ⟩ := helicoidReducedDistance_exists_min p
  refine ⟨p.1*cos θ+p.2.1*sin θ,θ,fun u φ => ?_⟩
  rw [helicoidSquaredDistance_reduced,helicoidSquaredDistance_reduced]
  simpa only [sub_self,zero_pow (by decide : 2 ≠ 0),zero_add] using
    (hθ φ).trans (le_add_of_nonneg_left (sq_nonneg _))

theorem helicoidSquaredDistance_r_hasDerivAt (p : ℝ × ℝ × ℝ) (r θ : ℝ) :
    HasDerivAt (fun u => helicoidSquaredDistance p u θ)
      (2*(r-(p.1*cos θ+p.2.1*sin θ))) r := by
  have hd := ((((hasDerivAt_id r).sub_const (p.1*cos θ+p.2.1*sin θ)).pow 2).add_const
    (helicoidReducedDistance p θ))
  convert hd using 1
  · funext u
    exact helicoidSquaredDistance_reduced p u θ
  · simp

theorem helicoidReducedDistance_hasDerivAt (p : ℝ × ℝ × ℝ) (θ : ℝ) :
    HasDerivAt (helicoidReducedDistance p)
      (2*(p.1*sin θ-p.2.1*cos θ)*(p.1*cos θ+p.2.1*sin θ)+2*(θ-p.2.2)) θ := by
  have hd := ((((hasDerivAt_sin θ).const_mul p.1).sub
    ((hasDerivAt_cos θ).const_mul p.2.1)).pow 2).add
    (((hasDerivAt_const θ p.2.2).sub (hasDerivAt_id θ)).pow 2)
  convert hd using 1
  · rfl
  · simp only [Pi.sub_apply,id_eq]
    ring

theorem helicoidSquaredDistance_min_is_normal {p : ℝ × ℝ × ℝ} {r θ : ℝ}
    (hmin : ∀ u φ : ℝ, helicoidSquaredDistance p r θ ≤ helicoidSquaredDistance p u φ) :
    ∃ s : ℝ, p = helicoidNormalMap r θ s ∧ helicoidSquaredDistance p r θ = s^2 := by
  have hm : IsLocalMin (fun u => helicoidSquaredDistance p u θ) r :=
    Filter.Eventually.of_forall (fun u => hmin u θ)
  have he := hm.hasDerivAt_eq_zero (helicoidSquaredDistance_r_hasDerivAt p r θ)
  have hr : r = p.1*cos θ+p.2.1*sin θ := by linarith
  have hmθ : IsLocalMin (helicoidReducedDistance p) θ := by
    apply Filter.Eventually.of_forall
    intro φ
    have hh := hmin (p.1*cos φ+p.2.1*sin φ) φ
    rw [helicoidSquaredDistance_reduced,helicoidSquaredDistance_reduced,hr] at hh
    simpa only [sub_self,zero_pow (by decide : 2 ≠ 0),zero_add] using hh
  have hθ := hmθ.hasDerivAt_eq_zero (helicoidReducedDistance_hasDerivAt p θ)
  let v := p.1*sin θ-p.2.1*cos θ
  have hz : p.2.2-θ = v*r := by rw [hr]; dsimp [v]; linarith [hθ]
  have hx : p.1 = r*cos θ+v*sin θ := by
    rw [hr]
    dsimp [v]
    nlinarith [congrArg (fun x : ℝ => p.1*x) (sin_sq_add_cos_sq θ)]
  have hy : p.2.1 = r*sin θ-v*cos θ := by
    rw [hr]
    dsimp [v]
    nlinarith [congrArg (fun x : ℝ => p.2.1*x) (sin_sq_add_cos_sq θ)]
  refine ⟨v*helicoidQ r,?_,?_⟩
  · apply Prod.ext
    · dsimp [helicoidNormalMap]
      rw [mul_div_cancel_right₀ _ (helicoidQ_pos r).ne']
      exact hx
    · apply Prod.ext
      · dsimp [helicoidNormalMap]
        rw [mul_div_cancel_right₀ _ (helicoidQ_pos r).ne']
        exact hy
      · dsimp [helicoidNormalMap,helicoidAngle]
        have hq := (helicoidQ_pos r).ne'
        field_simp
        nlinarith
  · rw [helicoidSquaredDistance_reduced,← hr]
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),zero_add]
    change v^2+(p.2.2-θ)^2 = (v*helicoidQ r)^2
    rw [hz,mul_pow,mul_pow,helicoidQ_sq]
    ring

theorem helicoidNormalMap_squaredDistance (r θ s : ℝ) :
    helicoidSquaredDistance (helicoidNormalMap r θ s) r θ = s^2 := by
  unfold helicoidSquaredDistance helicoidNormalMap helicoidAngle
  dsimp
  field_simp [(helicoidQ_pos r).ne']
  nlinarith [congrArg (fun x : ℝ => s^2*x) (sin_sq_add_cos_sq θ),
    congrArg (fun x : ℝ => s^2*x) (helicoidQ_sq r)]

/-- Every point in the explicit width-one normal tube has this base point as
its Euclidean nearest point, with squared distance exactly `s²`. -/
theorem helicoidNormalMap_nearest {r θ s : ℝ} (hs : |s| < 1) :
    ∀ u φ : ℝ, s^2 ≤ helicoidSquaredDistance (helicoidNormalMap r θ s) u φ := by
  obtain ⟨r₀,θ₀,hmin⟩ := helicoidSquaredDistance_exists_min (helicoidNormalMap r θ s)
  obtain ⟨s₀,he,hd⟩ := helicoidSquaredDistance_min_is_normal hmin
  have hle := hmin r θ
  rw [hd,helicoidNormalMap_squaredDistance] at hle
  have hs₀ : |s₀| < 1 := by
    have h := (sq_le_sq).mp hle
    exact h.trans_lt hs
  obtain ⟨hr,hθ,hss⟩ := helicoidNormalMap_injective hs hs₀ he
  subst r₀
  subst θ₀
  subst s₀
  intro u φ
  simpa only [helicoidNormalMap_squaredDistance] using hmin u φ

theorem helicoidNormalMap_nearest_unique {r θ s u φ : ℝ} (hs : |s| < 1)
    (hd : helicoidSquaredDistance (helicoidNormalMap r θ s) u φ = s^2) :
    u = r ∧ φ = θ := by
  have hmin : ∀ v ψ : ℝ, helicoidSquaredDistance (helicoidNormalMap r θ s) u φ ≤
      helicoidSquaredDistance (helicoidNormalMap r θ s) v ψ := by
    intro v ψ
    rw [hd]
    exact helicoidNormalMap_nearest hs v ψ
  obtain ⟨s₀,he,hsq⟩ := helicoidSquaredDistance_min_is_normal hmin
  have hs₀ : |s₀| < 1 := by
    have h := (sq_le_sq).mp (show s₀^2 ≤ s^2 by linarith)
    exact h.trans_lt hs
  obtain ⟨hr,hθ,_⟩ := helicoidNormalMap_injective hs hs₀ he
  exact ⟨hr.symm,hθ.symm⟩

/-- The actual distance-one neighborhood has a unique closest point. The
hypothesis uses the squared Euclidean distance, so does not assume a normal
coordinate representation. -/
theorem helicoid_distance_tube_unique_nearest {p : ℝ × ℝ × ℝ}
    (hp : ∃ r θ : ℝ, helicoidSquaredDistance p r θ < 1) :
    ∃! q : ℝ × ℝ, ∀ u φ : ℝ,
      helicoidSquaredDistance p q.1 q.2 ≤ helicoidSquaredDistance p u φ := by
  obtain ⟨u,φ,hp⟩ := hp
  obtain ⟨r,θ,hmin⟩ := helicoidSquaredDistance_exists_min p
  obtain ⟨s,he,hd⟩ := helicoidSquaredDistance_min_is_normal hmin
  have hs : |s| < 1 := (sq_lt_one_iff_abs_lt_one s).mp (by
    have h := hmin u φ
    rw [hd] at h
    linarith)
  refine ⟨(r,θ),hmin,?_⟩
  intro q hq
  have hsame : helicoidSquaredDistance p q.1 q.2 = s^2 := by
    have h1 := hmin q.1 q.2
    have h2 := hq r θ
    linarith
  rw [he] at hsame
  obtain ⟨h1,h2⟩ := helicoidNormalMap_nearest_unique hs hsame
  exact Prod.ext h1 h2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidSquaredDistance_exists_min
#print axioms TwoAxisHelicoid.helicoidNormalMap_nearest
#print axioms TwoAxisHelicoid.helicoid_distance_tube_unique_nearest
