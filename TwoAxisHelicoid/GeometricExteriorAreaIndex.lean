import TwoAxisHelicoid.ExteriorChartTestFunctions
import TwoAxisHelicoid.ExteriorNormalTestSmooth
import TwoAxisHelicoid.ExteriorInverseCompactAvoidance
import TwoAxisHelicoid.ExteriorWeierstrassDerivative
import TwoAxisHelicoid.RecenteredHelicoidAreaIndex

namespace TwoAxisHelicoid
open Complex Matrix Set Function Filter Bornology MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

/-- An actual variation of the entire surface, with scalar displacement
measured along the normal obtained in the height chart. Whenever the
scalar test vanishes this map is exactly the starting position. -/
noncomputable def exteriorSurfaceVariation {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (W : ℂ → ℂ)
    (u : M → ℝ) (s : ℝ) (x : M) : Fin 3 → ℝ :=
  X x+s • (u x • holomorphicLogGaussNormal W (e x-c))

/-- For every compact part of the original surface and every dimension,
there are independent smooth scalar tests on the entire surface. Their
actual normal variations fix the complement of a common compact patch
and the Hessian of the area on that patch is negative definite. -/
theorem geometric_exterior_actual_area_infinite_index {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (hc : Continuous X)
    (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricExteriorCoordinate X) :
    ∃ (c : ℂ) (f : ℂ → ℂ), AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
    ∀ C : Set M, IsCompact C → ∀ n : ℕ, ∃ (K : Set (ℝ × ℝ)) (U : Fin n → M → ℝ),
      let e := A.chart
      let W := fun z : ℂ => I*(A.pitch:ℂ)*z+infinityCorrection f z
      let P := e.symm '' (translatedPlaneCoordinates c '' K)
      let variation := fun (a : Fin n → ℝ) => exteriorSurfaceVariation X e c W (fun x => ∑ i, a i*U i x)
      IsCompact K ∧ (∀ p ∈ K, translatedPlaneCoordinates c p ∈ e.target) ∧ IsCompact P ∧ Disjoint P C ∧
      (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (U i) ∧ tsupport (U i) ⊆ P) ∧ LinearIndependent ℝ U ∧
      (∀ p ∈ K, ∀ w : ℂ, holomorphicLogGaussNormal W (planeComplex p) ⬝ᵥ
        fderiv ℝ (fun z => X (e.symm (z+c))) (planeComplex p) w = 0) ∧
      (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (fun x => U i x • holomorphicLogGaussNormal W (e x-c))) ∧
      (∀ a s x, x ∉ P → variation a s x = X x) ∧
      ∀ a : Fin n → ℝ, a ≠ 0 → deriv (deriv (fun s : ℝ => ∫ p in K,
        coordinateAreaDensity (fun z => variation a s (e.symm (z+c))) (planeComplex p))) 0 < 0 := by
  obtain ⟨c,f,hf,hf0,⟨D,hD⟩,hind⟩ := recentered_analytic_helicoid_area_index A.pitch_ne A.correction A.analytic
    (geometric_exterior_coordinate_weierstrass X hX A)
  refine ⟨c,f,hf,hf0,?_⟩
  intro C hC n
  let e := A.chart
  let T := translatedPlaneCoordinates c
  let W := fun z : ℂ => I*(A.pitch:ℂ)*z+infinityCorrection f z
  have hsing := (geometric_exterior_inverse_escapes top X hc A).eventually hC.compl_mem_cocompact
  obtain ⟨B,_,hB⟩ := hasBasis_cobounded_norm.eventually_iff.mp hsing
  obtain ⟨R,_,hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp (infinityCorrection_eventually_analytic hf)
  obtain ⟨K,v,hK,hfar,hv,hl,hneg⟩ := hind (max (max R D) (max B A.radius+‖c‖+1)) n
  have hbound (p) (hp : p ∈ K) : max B A.radius < ‖T p‖ := by
    have h := (hfar p hp).trans_le (norm_le_planeComplex_norm p)
    have h' := norm_sub_le (planeComplex p+c) c
    rw [add_sub_cancel_right] at h'
    rw [show T p = planeComplex p+c from translatedPlaneCoordinates_apply c p]
    linarith [le_max_right (max R D) (max B A.radius+‖c‖+1)]
  have htarget p (hp : p ∈ K) : T p ∈ e.target := A.target ▸ (le_max_right B _).trans_lt (hbound p hp)
  have hcomp := (hK.image T.continuous).image_of_continuousOn (e.symm.continuousOn.mono
    (show T '' K ⊆ e.target from by rintro _ ⟨p,hp,rfl⟩; exact htarget p hp))
  obtain ⟨U,hU,hlin,hval⟩ := exterior_chart_global_tests e A.holomorphic c hK htarget v hv hl
  refine ⟨K,U,hK,htarget,hcomp,Set.disjoint_left.mpr ?_,hU,hlin,?_,?_,?_,?_⟩
  · rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
    exact hB (show B ≤ ‖T p‖ from (le_max_left _ _).trans (hbound p hp).le)
  · intro p hp w
    have hz : D ≤ ‖planeComplex p‖ := (le_max_right R D).trans ((le_max_left _ _).trans
      ((hfar p hp).le.trans (norm_le_planeComplex_norm p)))
    exact log_gauss_normal_perpendicular (hD _ hz) w
  · intro i
    refine compact_exterior_normal_test_smooth e A.holomorphic c hcomp ?_ (hU i).1 (hU i).2 ?_
    · rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
      exact e.map_target (htarget p hp)
    · rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
      rw [e.right_inv (htarget p hp),translatedPlaneCoordinates_apply,add_sub_cancel_right]
      have hz : R ≤ ‖planeComplex p‖ := (le_max_left R D).trans ((le_max_left _ _).trans ((hfar p hp).le.trans (norm_le_planeComplex_norm p)))
      exact (analyticAt_const.mul analyticAt_id).add (hR hz)
  · intro a s x hx
    have hi (i : Fin n) : U i x = 0 := by
      by_contra hn
      exact hx ((hU i).2 (subset_closure hn))
    simp [exteriorSurfaceVariation,hi]
  · intro a ha
    have heq (s : ℝ) : (∫ p in K, coordinateAreaDensity
        (fun z => exteriorSurfaceVariation X e c W (fun x => ∑ i, a i*U i x) s (e.symm (z+c))) (planeComplex p)) =
        ∫ p in K, coordinateVariationDensity (fun z => X (e.symm (z+c))) W (fun p => ∑ i, a i*v i p) s p := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p hp
      apply coordinateAreaDensity_congr_local
      have hz : planeComplex p+c ∈ e.target := translatedPlaneCoordinates_apply c p ▸ htarget p hp
      filter_upwards [(continuousAt_id.add continuousAt_const).eventually (e.open_target.mem_nhds hz)] with z hzt
      change z+c ∈ e.target at hzt
      have hid : planeComplex (z.re,z.im) = z := by apply Complex.ext <;> simp only [planeComplex_re,planeComplex_im]
      have ht : T (z.re,z.im) = z+c := (translatedPlaneCoordinates_apply _ _).trans (congrArg (·+c) hid)
      have hu (i) : U i (e.symm (z+c)) = v i (z.re,z.im) := by
        rw [← ht]
        exact hval i _ (ht ▸ hzt)
      simp only [exteriorSurfaceVariation,weierstrassNormalVariation,scalarComplexLift,
        e.right_inv hzt,add_sub_cancel_right,hu]
    change deriv (deriv _) 0 < 0
    rw [funext heq]
    exact hneg a ha

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.geometric_exterior_actual_area_infinite_index
