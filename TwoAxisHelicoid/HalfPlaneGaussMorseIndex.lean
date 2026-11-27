import TwoAxisHelicoid.ReciprocalGaussEndChart
import TwoAxisHelicoid.VariableHeightCompactArea
import TwoAxisHelicoid.CompactHelicoidTestFamily
import TwoAxisHelicoid.GeometricExteriorAreaIndex
import TwoAxisHelicoid.SurfaceMorseIndex

namespace TwoAxisHelicoid
open Complex Matrix Set Function Filter Bornology MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

/-- The actual unit Gauss normal is perpendicular to both tangent
directions for any nonzero complex height coefficient. -/
private theorem regular_height_normal_perpendicular {Y : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {z h : ℂ}
    (hd : HasFDerivAt Y (nullRealDerivative (weierstrassTriple (exp (W z)) h)) z) (nh : h≠0) (v : ℂ) :
    holomorphicLogGaussNormal W z ⬝ᵥ fderiv ℝ Y z v=0 := by
  let L := nullRealDerivative (weierstrassTriple (exp (W z)) h)
  have f := variable_height_log_gauss_frame (W z) 0 h nh
  rw [hd.fderiv]
  change logGaussSphere (W z).re (W z).im ⬝ᵥ L v=0
  rw [real_complex_map_columns L v,dotProduct_add,dotProduct_smul,dotProduct_smul,f.na,f.nb]
  simp

/-- Two meromorphic poles in a genuine end chart force infinite
compactly supported Morse index directly on the surface. The original
surface need not already have a torus uniformization. -/
theorem geometric_double_pole_end_infinite_morse_index {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricDoublePoleEnd X) :
    HasInfiniteCompactSurfaceMorseIndex X := by
  obtain ⟨e,B,W,h,hol,esc,sheet,asym⟩ := geometric_double_pole_gauss_half_plane charts A
  intro C hC n
  obtain ⟨D,_,hD⟩ := hasBasis_cobounded_norm.eventually_iff.mp (esc.eventually hC.compl_mem_cocompact)
  obtain ⟨K,v,ε,hK,ep,vs,vl,neg⟩ := robust_compact_helicoid_test_family n
  obtain ⟨c,_,patch⟩ := gauss_log_half_plane_potential_on_compact asym hK ep (max B D)
  let T := translatedPlaneCoordinates c
  let ξ := fun z : ℂ => e.symm (z+c)
  let G := fun z : ℂ => W (z+c)
  let H := fun z : ℂ => h (z+c)
  let Y := X ∘ ξ
  let P := e.symm '' (T '' K)
  have info p (hp : p∈K) := sheet (planeComplex p+c) ((le_max_left B D).trans_lt (patch p hp).1)
  have target p (hp : p∈K) : T p∈e.target := translatedPlaneCoordinates_apply c p ▸ (info p hp).1
  have avoid p (hp : p∈K) : e.symm (T p)∉C := hD ((le_max_right B D).trans
    ((patch p hp).1.le.trans (translatedPlaneCoordinates_apply c p ▸ re_le_norm (planeComplex p+c))))
  have compact : IsCompact P := (hK.image T.continuous).image_of_continuousOn
    (e.symm.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact target p hp))
  have gA p (hp : p∈K) : AnalyticAt ℂ G (planeComplex p) := (info p hp).2.1.comp (f := fun z : ℂ => z+c) (analyticAt_id.add analyticAt_const)
  have hA p (hp : p∈K) : AnalyticAt ℂ H (planeComplex p) := (info p hp).2.2.1.comp (f := fun z : ℂ => z+c) (analyticAt_id.add analyticAt_const)
  have hn p (hp : p∈K) : H (planeComplex p)≠0 := (info p hp).2.2.2.1
  have yd p (hp : p∈K) : HasFDerivAt Y (nullRealDerivative (weierstrassTriple (exp (G (planeComplex p))) (H (planeComplex p)))) (planeComplex p) := by
    simpa only [Y,ξ,G,H,Function.comp_def,ContinuousLinearMap.comp_id] using!
      ((info p hp).2.2.2.2.comp (planeComplex p) ((hasFDerivAt_id (𝕜 := ℝ) _).add_const c))
  have hco : ContinuousOn (H ∘ planeComplex) K := fun p hp => ((hA p hp).continuousAt.comp planeComplex_continuous.continuousAt).continuousWithinAt
  have potential : ContinuousOn (gaussNormalDirichletDensity G) K := by
    let V := fun p => 2*‖deriv G (planeComplex p)‖^2/(Real.cosh (G (planeComplex p)).re)^2
    have den : ContinuousOn (fun p => G (planeComplex p)) K := fun p hp =>
      ((gA p hp).continuousAt.comp planeComplex_continuous.continuousAt).continuousWithinAt
    have num : ContinuousOn (fun p => deriv G (planeComplex p)) K := fun p hp =>
      ((gA p hp).deriv.continuousAt.comp planeComplex_continuous.continuousAt).continuousWithinAt
    have cden := Real.continuous_cosh.comp_continuousOn (Complex.continuous_re.comp_continuousOn den)
    have co : ContinuousOn V K := (continuousOn_const.mul (num.norm.pow 2)).div (cden.pow 2)
      (fun p _ => pow_ne_zero _ (Real.cosh_pos _).ne')
    exact co.congr fun p hp => gaussNormalDirichletDensity_formula (gA p hp).differentiableAt.hasDerivAt
  have energies := neg (gaussNormalDirichletDensity G) potential (fun p hp => (patch p hp).2.2)
  obtain ⟨U,u,ind,uv⟩ := exterior_chart_global_tests e hol c hK target v vs vl
  let N := fun x : M => holomorphicLogGaussNormal G (e x-c)
  have normform p (hp : p∈K) : e (ξ (planeComplex p))-c=planeComplex p := by
    change e (e.symm (planeComplex p+c))-c=_
    rw [e.right_inv (translatedPlaneCoordinates_apply c p ▸ target p hp),add_sub_cancel_right]
  have unit p (hp : p∈K) : N (ξ (planeComplex p)) ⬝ᵥ N (ξ (planeComplex p))=1 := by
    dsimp only [N]
    rw [normform p hp]
    simpa only [dotProduct,pow_two] using (holomorphicLogGaussNormal_actual_weierstrass_normal G (planeComplex p)).1
  have nn (x) (hx : x∈P) : N x≠0 := by
    obtain ⟨_,⟨p,hp,rfl⟩,rfl⟩ := hx
    rw [translatedPlaneCoordinates_apply]
    intro eq
    have e := unit p hp
    change N (ξ (planeComplex p))=0 at eq
    rw [eq,zero_dotProduct] at e
    exact zero_ne_one e
  refine ⟨e,c,K,U,N,hol,hK,target,compact,?_,u,ind,?_,?_ ,
    independent_compact_normal_multiples U N ind (fun i => (u i).2) nn,?_,?_⟩
  · exact disjoint_left.mpr (by rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩; exact avoid p hp)
  · intro p hp
    refine ⟨unit p hp,fun w => ?_⟩
    change holomorphicLogGaussNormal G (e (ξ (planeComplex p))-c) ⬝ᵥ fderiv ℝ Y (planeComplex p) w=0
    rw [normform p hp]
    exact regular_height_normal_perpendicular (yd p hp) (hn p hp) w
  · intro i
    apply compact_exterior_normal_test_smooth e hol c compact _ (u i).1 (u i).2
    · rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
      rw [e.right_inv (target p hp),translatedPlaneCoordinates_apply,add_sub_cancel_right]
      exact gA p hp
    · rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩
      exact e.map_target (target p hp)
  · intro a s x hx
    have zero (i : Fin n) : U i x=0 := by by_contra nz; exact hx ((u i).2 (subset_closure nz))
    simp [zero]
  · intro a na
    let vA := fun p => ∑ i, a i*v i p
    have sm : ContDiff ℝ ∞ vA := by have hv i := (vs i).1; dsimp [vA]; fun_prop
    have sA := finite_test_sum_tsupport_subset hK.isClosed (fun i => (vs i).2) a
    have dA := compact_variable_height_area_second_derivative hK sA sm hn hco yd gA
    have eq (s : ℝ) : (∫ p in K,coordinateAreaDensity
        ((fun x => X x+s • ((∑ i,a i*U i x) • N x)) ∘ ξ) (planeComplex p))=
        ∫ p in K,coordinateVariationDensity Y G vA s p := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p hp
      apply coordinateAreaDensity_congr_local
      have target' : planeComplex p+c∈e.target := translatedPlaneCoordinates_apply c p ▸ target p hp
      filter_upwards [(continuousAt_id.add continuousAt_const).eventually (e.open_target.mem_nhds target')] with z hz
      change z+c∈e.target at hz
      have idz : planeComplex (z.re,z.im)=z := by apply Complex.ext <;> simp [planeComplex]
      have tz : T (z.re,z.im)=z+c := (translatedPlaneCoordinates_apply _ _).trans (congrArg (·+c) idz)
      have eval i : U i (ξ z)=v i (z.re,z.im) := by change U i (e.symm (z+c))=_; rw [← tz]; exact uv i _ (tz ▸ hz)
      simp only [Function.comp_apply,Y,eval,N,ξ,e.right_inv hz,add_sub_cancel_right,weierstrassNormalVariation,vA,scalarComplexLift]
    change deriv (deriv _) 0<0
    rw [funext eq]
    exact dA.deriv.trans_lt (energies a na)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_double_pole_end_infinite_morse_index
