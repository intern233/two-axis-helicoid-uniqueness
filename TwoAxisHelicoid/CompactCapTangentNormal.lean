import TwoAxisHelicoid.PuncturedMarkedTangentFrame
import TwoAxisHelicoid.PuncturedNormalExtension
import TwoAxisHelicoid.ImmersionChartReparametrization
import TwoAxisHelicoid.TorusFundamentalGenerators

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix
open scoped ContDiff Manifold Matrix
set_option maxHeartbeats 700000

/-- Two genuinely regular spatial parametrizations of the same surface
germ have the same unoriented normal. The coordinate change is only
assumed continuous; its differentiability follows from the immersion. -/
theorem spatial_normal_of_immersion_germ {Y Z : ℂ → Fin 3 → ℝ} {k : ℂ → ℂ} {x : ℂ}
    (hY : ContDiffAt ℝ ∞ Y x) (hiY : Function.Injective (fderiv ℝ Y x))
    (hZ : ContDiffAt ℝ ∞ Z (k x)) (hiZ : Function.Injective (fderiv ℝ Z (k x)))
    (hk : ContinuousAt k x) (he : Z ∘ k =ᶠ[𝓝 x] Y) :
    let a := tangentPairNormal (spatialDifferentialFrame hiY (v := 1) one_ne_zero)
    let b := tangentPairNormal (spatialDifferentialFrame hiZ (v := 1) one_ne_zero)
    a = b ∨ a = -b := by
  have hD := (contDiffAt_of_comp_immersion hZ hiZ hk (hY.congr_of_eventuallyEq he)).differentiableAt (by simp)
  have hE : fderiv ℝ Y x = (fderiv ℝ Z (k x)).comp (fderiv ℝ k x) :=
    he.fderiv_eq.symm.trans (fderiv_comp x (hZ.differentiableAt (by simp)) hD)
  have hr : LinearMap.range (fderiv ℝ Y x).toLinearMap ≤ LinearMap.range (fderiv ℝ Z (k x)).toLinearMap := by
    rintro _ ⟨v,rfl⟩
    exact ⟨fderiv ℝ k x v,(congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D v) hE).symm⟩
  rcases spatial_differential_normal_eq_or_neg hiZ hiY hr with ha | ha
  · exact Or.inl ha.symm
  · right
    rw [ha,neg_neg]

theorem regular_immersion_chart_complex_at {M : Type*} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (ℝ × ℝ) M] [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M] {F : M → Fin 3 → ℝ}
    (hF : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p))
    {p b : M} (hb : p ≠ b) :
    ∃ e : OpenPartialHomeomorph M ℂ, RegularImmersionChart F e ∧ p ∈ e.source := by
  obtain ⟨e,he,_,hpe⟩ := punctured_immersion_regular_charts (p := b) (fun x _ => hF x) (fun x _ => hi x) p hb
  exact ⟨e.trans Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph,
    regularImmersionChart_reparametrize he Complex.equivRealProdCLM.symm,⟨hpe,mem_univ _⟩⟩

/-- The ambient unit normal of a cap, with orientation prescribed by its
actual derivative on the original marked punctured torus. The normal at
the new point is obtained from a genuine regular cap chart. -/
theorem compact_cap_unit_normal_extends (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)) [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L)]
    (hFc : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hci : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (hF : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q)) :
    ∃ n : C(PeriodTorus L,Fin 3 → ℝ),
      (∀ q, n q ⬝ᵥ n q = 1) ∧
      (∀ q : PuncturedPeriodTorus L, n q.1 = tangentPairNormal (puncturedMarkedTangentFrame L F hF hi q)) ∧
      ∃ (e : OpenPartialHomeomorph (PeriodTorus L) ℂ) (he : RegularImmersionChart F e) (h0 : 0 ∈ e.source),
        let N := tangentPairNormal (spatialDifferentialFrame (he (e 0) (e.map_source h0)).2 (v := 1) one_ne_zero)
        n 0 = N ∨ n 0 = -N := by
  obtain ⟨e,he,h0⟩ := regular_immersion_chart_complex_at hFc hci (puncturedTorusCenter L).2.symm
  obtain ⟨V,_,hV,h0V,hVe,_,hconn⟩ := centered_surface_chart_neighborhood
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ) e h0
  let P := puncturedMarkedTangentFrame L F hF hi
  let f : C(PuncturedPeriodTorus L,Fin 3 → ℝ) := ⟨tangentPairNormal ∘ P,tangentPairNormal_continuous.comp P.continuous⟩
  let D := fun q : V => fderiv ℝ (F ∘ e.symm) (e q.1)
  have hreg (q : V) := he (e q.1) (e.map_source (hVe q.2))
  have hDc : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hqc : ContinuousAt (fun v : V => e v.1) q :=
      (e.continuousAt (hVe q.2)).comp (f := (Subtype.val : V → PeriodTorus L)) continuous_subtype_val.continuousAt
    exact ((hreg q).1.continuousAt_fderiv (by simp)).comp (f := fun v : V => e v.1) hqc
  let g' : C(V,OrthonormalTangentPair) := ⟨fun q => spatialDifferentialFrame (hreg q).2 (v := 1) one_ne_zero,
    spatialDifferentialFrame_continuous hDc continuous_const _ _⟩
  let g : C(V,Fin 3 → ℝ) := ⟨tangentPairNormal ∘ g',tangentPairNormal_continuous.comp g'.continuous⟩
  have hsign (q : V) (hq : q.1 ≠ 0) : f ⟨q.1,hq⟩ = g q ∨ f ⟨q.1,hq⟩ = -g q := by
    obtain ⟨z,hz⟩ := puncturedPlaneProjection_surjective L ⟨q.1,hq⟩
    have hπq : periodTorusProjection L z.1 = q.1 := congrArg Subtype.val hz
    have hπ : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
    let k := e ∘ periodTorusProjection L
    have hse : periodTorusProjection L z.1 ∈ e.source := hπq ▸ hVe q.2
    have hk : ContinuousAt k z.1 := (e.continuousAt hse).comp (f := periodTorusProjection L) hπ.continuousAt
    have hc : (F ∘ e.symm) ∘ k =ᶠ[𝓝 z.1] F ∘ periodTorusProjection L := by
      filter_upwards [hπ.continuousAt.eventually (e.open_source.mem_nhds hse)] with w hw
      exact congrArg F (e.left_inv hw)
    have hZ := he (k z.1) (e.map_source hse)
    have hY := spatial_torus_lift_regular_at L F z.2 hF hi
    have h := spatial_normal_of_immersion_germ hY.1 hY.2 hZ.1 hZ.2 hk hc
    have hfq : f ⟨q.1,hq⟩ = tangentPairNormal (puncturedPlaneGramFrame L F hF hi z) := by
      change tangentPairNormal (P ⟨q.1,hq⟩) = _
      rw [← hz,puncturedMarkedTangentFrame_projection]
    rw [hfq]
    have hnk : k z.1 = e q.1 := congrArg e hπq
    have hframe : spatialDifferentialFrame hZ.2 (v := 1) one_ne_zero = g' q := by
      apply Subtype.ext
      change spatialGramFrame (fderiv ℝ (F ∘ e.symm) (k z.1) 1) _ = spatialGramFrame (fderiv ℝ (F ∘ e.symm) (e q.1) 1) _
      rw [hnk]
    change tangentPairNormal (puncturedPlaneGramFrame L F hF hi z) = tangentPairNormal (spatialDifferentialFrame hZ.2 (v := 1) one_ne_zero) ∨
      tangentPairNormal (puncturedPlaneGramFrame L F hF hi z) = -tangentPairNormal (spatialDifferentialFrame hZ.2 (v := 1) one_ne_zero) at h
    rw [hframe] at h
    exact h
  obtain ⟨n,hn,hg⟩ := punctured_unit_normal_extends 0 hV h0V hconn f g
    (fun q => tangentPairNormal_ne_zero (g' q)) hsign
  have h0sign : n 0 = g ⟨0,h0V⟩ ∨ n 0 = -g ⟨0,h0V⟩ :=
    hg.imp (fun h => h ⟨0,h0V⟩) (fun h => h ⟨0,h0V⟩)
  refine ⟨n,?_,hn,e,he,h0,h0sign⟩
  intro q
  by_cases hq : q ≠ 0
  · rw [hn ⟨q,hq⟩]
    exact tangentPairNormal_dot_self _
  · have hq0 := not_ne_iff.mp hq
    subst q
    rcases h0sign with h | h
    · rw [h]
      exact tangentPairNormal_dot_self _
    · rw [h,neg_dotProduct,dotProduct_neg,neg_neg]
      exact tangentPairNormal_dot_self _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_cap_unit_normal_extends
