import TwoAxisHelicoid.ActualAreaVariationIndex

namespace TwoAxisHelicoid
open Set Function MeasureTheory
open scoped ContDiff

/-- A single compact patch of the standard helicoid supplies any fixed
number of disjoint tests. Their span stays strictly negative for every
potential uniformly close on this patch. -/
theorem robust_compact_helicoid_test_family (n : ℕ) :
    ∃ (K : Set (ℝ × ℝ)) (v : Fin n → ℝ × ℝ → ℝ) (ε : ℝ), IsCompact K ∧ 0<ε ∧
      (∀ i, ContDiff ℝ ∞ (v i) ∧ tsupport (v i)⊆K) ∧ LinearIndependent ℝ v ∧
      ∀ W : ℝ × ℝ → ℝ, ContinuousOn W K → (∀ p∈K, |W p-2*helicoidGroundState p.2^2|≤ε) →
      ∀ c : Fin n → ℝ, c≠0 → planarQuadraticEnergy W (fun p => ∑ i, c i*v i p)<0 := by
  let V := fun y => 2*helicoidGroundState y^2
  have cv : Continuous V := by unfold V helicoidGroundState; fun_prop (disch := intros; positivity)
  have vn y : 0≤V y := by dsimp [V]; positivity
  have vp : 0<V 0 := by norm_num [V,helicoidGroundState]
  obtain ⟨u,hu,su,neg⟩ := exists_planar_smooth_compact_negative_direction cv vn vp
  let P := fun p : ℝ × ℝ => V p.2
  have cp : Continuous P := cv.comp continuous_snd
  have qn : planarQuadraticEnergy P u<0 := by rwa [planarQuadraticEnergy_eq_schrodinger (hu.differentiable (by simp))]
  have mass : 0≤planarMass u := integral_nonneg fun p => sq_nonneg (u p)
  let ε := -planarQuadraticEnergy P u/(2*(planarMass u+1))
  have ep : 0<ε := div_pos (neg_pos.mpr qn) (by linarith)
  have margin : ε*planarMass u < -planarQuadraticEnergy P u := by
    have denom : 0<2*(planarMass u+1) := by linarith
    apply (mul_lt_mul_iff_right₀ denom).mp
    dsimp [ε]
    field_simp
    nlinarith
  obtain ⟨s,_,disj⟩ := finite_disjoint_far_translates su 0 n
  let v := fun i => planarTranslate u (s i)
  let K := ⋃ i, tsupport (v i)
  have hv i : ContDiff ℝ ∞ (v i) := planarTranslate_contDiff hu _
  have hs i : HasCompactSupport (v i) := planarTranslate_hasCompactSupport su _
  have compact : IsCompact K := isCompact_iUnion hs
  have sup i : tsupport (v i)⊆K := subset_iUnion (fun j => tsupport (v j)) i
  have eq (i) : planarQuadraticEnergy P (v i)=planarQuadraticEnergy P u := by
    change planarQuadraticEnergy P (planarTranslate u (s i))=_
    rw [planarQuadraticEnergy_translate (hu.differentiable (by simp))]
    simp [P]
  have qv i : planarQuadraticEnergy P (v i)<0 := (eq i).trans_lt qn
  refine ⟨K,v,ε,compact,ep,fun i => ⟨hv i,sup i⟩,planar_negative_disjoint_family_independent cp hv hs disj qv,?_⟩
  intro W cw close c nc
  let f : C(K,ℝ) := ⟨fun p => W p,continuousOn_iff_continuous_domRestrict.mp cw⟩
  obtain ⟨U,he⟩ := ContinuousMap.exists_restrict_eq compact.isClosed f
  have coincide {p : ℝ × ℝ} (hp : p∈K) : U p=W p := congrArg (fun g : C(K,ℝ) => g ⟨p,hp⟩) he
  have nv i : planarQuadraticEnergy U (v i)<0 := by
    apply planarQuadraticEnergy_negative_of_close U.continuous cp (hv i) (hs i) (ε := ε)
    · intro p hp
      rw [coincide (sup i hp)]
      exact close p (sup i hp)
    · rw [eq i,show planarMass (v i)=planarMass u from planarMass_translate _ _]
      exact margin
  have e := planarQuadraticEnergy_eq_of_agree_on_support (W := W) (V := U)
    (v := fun p => ∑ i, c i*v i p) (fun p hp => (coincide (finite_test_sum_tsupport_subset compact.isClosed sup c (subset_closure hp))).symm)
  exact e.trans_lt (planarQuadraticEnergy_disjoint_sum_negative U.continuous hv hs disj nv nc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.robust_compact_helicoid_test_family
