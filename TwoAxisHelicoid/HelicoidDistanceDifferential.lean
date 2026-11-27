import TwoAxisHelicoid.HelicoidTubeCurve

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff

theorem helicoid_inverse_curve_differential {x : ℝ → HelicoidTubeCoordinates}
    {v : HelicoidTubeCoordinates} {τ : ℝ} (hx : HasDerivAt x v τ)
    (hy : x τ ∈ helicoidTubeEquiv.target) :
    let p := helicoidTubeEquiv.symm (x τ)
    let w := (fderiv ℝ helicoidTubeEquiv.symm (x τ)) v
    HasDerivAt (fun t => helicoidTubeEquiv.symm (x t)) w τ ∧
      (fun i => w.1.2*helicoidTubeR p.1.2 p.2 p.1.1 i+
        w.2*helicoidTubeTheta p.1.2 p.2 p.1.1 i+
        w.1.1*standardHelicoidNormal p.1.2 p.2 i) = tubeCartesian v := by
  dsimp only
  have hi := ((helicoidTubeEquiv_inverse_contDiffAt hy).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt τ hx
  refine ⟨hi,?_⟩
  have hd := helicoidTube_curve_hasDerivAt hi.fst.snd hi.snd hi.fst.fst
  have he : (fun t => tubeCartesian (x t)) =ᶠ[𝓝 τ]
      (fun t => tubeCartesian (helicoidTubeMap (helicoidTubeEquiv.symm (x t)))) := by
    filter_upwards [hx.continuousAt.eventually (helicoidTubeEquiv_target_isOpen.mem_nhds hy)] with t ht
    change tubeCartesian (x t) = tubeCartesian (helicoidTubeEquiv (helicoidTubeEquiv.symm (x t)))
    rw [helicoidTubeEquiv.right_inv ht]
  exact (hd.congr_of_eventuallyEq he).unique (tubeCartesian_hasDerivAt hx)

/-- The derivative of the actual signed Euclidean distance along every
differentiable curve is the scalar product with the actual unit normal. -/
theorem helicoidSignedDistance_curve_hasDerivAt {x : ℝ → HelicoidTubeCoordinates}
    {v : HelicoidTubeCoordinates} {τ : ℝ} (hx : HasDerivAt x v τ)
    (hy : x τ ∈ helicoidTubeEquiv.target) :
    HasDerivAt (fun t => helicoidSignedDistance (x t))
      (∑ i, helicoidNormalField (x τ) i*tubeCartesian v i) τ := by
  obtain ⟨hi,he⟩ := helicoid_inverse_curve_differential hx hy
  have hd := helicoidTube_vector_dot_normal
    (helicoidTubeEquiv.symm (x τ)).1.2 (helicoidTubeEquiv.symm (x τ)).2
    (helicoidTubeEquiv.symm (x τ)).1.1
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).1.2
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).2
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).1.1
  simp_rw [congrFun he] at hd
  change (∑ i, helicoidNormalField (x τ) i*tubeCartesian v i) =
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).1.1 at hd
  rw [hd]
  exact hi.fst.fst

/-- The actual normal field along a curve in the half-width distance tube
has a derivative whose Euclidean norm is at most twice the curve speed. -/
theorem helicoidNormalField_curve_derivative_bound {x : ℝ → HelicoidTubeCoordinates}
    {v : HelicoidTubeCoordinates} {τ : ℝ} (hx : HasDerivAt x v τ)
    (hy : x τ ∈ helicoidTubeEquiv.target) (hs : |helicoidSignedDistance (x τ)| ≤ 1/2) :
    ∃ n : Fin 3 → ℝ, HasDerivAt (fun t => helicoidNormalField (x t)) n τ ∧
      (∑ i, (n i)^2) ≤ 4*(∑ i, (tubeCartesian v i)^2) := by
  obtain ⟨hi,he⟩ := helicoid_inverse_curve_differential hx hy
  have hn := standardHelicoidNormal_curve_hasDerivAt hi.fst.snd hi.snd
  refine ⟨_,hn,?_⟩
  have h := helicoid_half_tube_normal_differential_bound
    (r := (helicoidTubeEquiv.symm (x τ)).1.2) (θ := (helicoidTubeEquiv.symm (x τ)).2)
    (s := (helicoidTubeEquiv.symm (x τ)).1.1) hs
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).1.2
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).2
    ((fderiv ℝ helicoidTubeEquiv.symm (x τ)) v).1.1
  simp_rw [congrFun he] at h
  exact h

theorem helicoidSignedDistance_fderiv {y v : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    (fderiv ℝ helicoidSignedDistance y) v =
      ∑ i, helicoidNormalField y i*tubeCartesian v i := by
  have hx : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hmember : y+(0 : ℝ) • v ∈ helicoidTubeEquiv.target := by simpa using hy
  have h1 := helicoidSignedDistance_curve_hasDerivAt hx hmember
  have h2 := ((helicoidSignedDistance_contDiffAt hmember).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hx
  simpa using h2.unique h1

/-- Coordinate form of the Euclidean Hessian operator bound: the gradient
of the actual signed distance is the normal field, and its derivative has
Euclidean squared norm at most four times that of the input vector. -/
theorem helicoidSignedDistance_hessian_bound {y v : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) (hs : |helicoidSignedDistance y| ≤ 1/2) :
    (∑ i, (((fderiv ℝ helicoidNormalField y) v) i)^2) ≤
      4*(∑ i, (tubeCartesian v i)^2) := by
  have hx : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hmember : y+(0 : ℝ) • v ∈ helicoidTubeEquiv.target := by simpa using hy
  have hsmall : |helicoidSignedDistance (y+(0 : ℝ) • v)| ≤ 1/2 := by simpa using hs
  obtain ⟨n,hn,hbound⟩ := helicoidNormalField_curve_derivative_bound hx hmember hsmall
  have hd := ((helicoidNormalField_contDiffAt hmember).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hx
  have he : (fderiv ℝ helicoidNormalField y) v = n := by simpa using hd.unique hn
  rwa [he]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidSignedDistance_fderiv
#print axioms TwoAxisHelicoid.helicoidSignedDistance_hessian_bound
