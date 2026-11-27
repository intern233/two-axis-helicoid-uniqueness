import TwoAxisHelicoid.TangentPlaneGramMembership
import TwoAxisHelicoid.TransverseBoundarySpin
import TwoAxisHelicoid.TorusSpinDetectsEssentialLoops

namespace TwoAxisHelicoid
open Complex Set Metric

noncomputable def spinCircleParameter (x : ℝ) : ℂ := Circle.exp (2*Real.pi*x)

theorem spinCircleParameter_hasDerivAt (x : ℝ) :
    HasDerivAt spinCircleParameter ((2*Real.pi) • (I*spinCircleParameter x)) x := by
  let k : ℝ := 2*Real.pi
  have hin : HasDerivAt (fun x : ℝ => (k*x : ℝ)) k x := by simpa using (hasDerivAt_id x).const_mul k
  have hc : HasDerivAt (fun x : ℝ => ((k*x : ℝ) : ℂ)*I) ((k:ℂ)*I) x := by
    exact ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hin).mul_const I)
  apply (hc.cexp).congr_deriv
  change Complex.exp ((↑(k*x):ℂ)*I) * ((k:ℂ)*I) = k • (I*Complex.exp ((↑(k*x):ℂ)*I))
  rw [Complex.real_smul]
  ring

/-- A transverse regular disk spanning a simple essential curve of a
regular marked torus makes the induced spin even. The only disk input
is the actual spatial parametrization, its regularity, and the stated
geometric boundary and transversality conditions. -/
theorem torus_with_compressing_disk_even (L : PeriodPair)
    {F : PeriodTorus L → Fin 3 → ℝ} (hF : Differentiable ℝ (F ∘ periodTorusProjection L))
    (hFD : Continuous (fderiv ℝ (F ∘ periodTorusProjection L)))
    (hFi : ∀ z, Function.Injective (fderiv ℝ (F ∘ periodTorusProjection L) z))
    {ξ : ℝ → ℂ} (hξ : ContDiff ℝ 1 ξ) {ω : ℂ} (hω : ω ≠ 0) (hωL : ω ∈ L.lattice)
    (hp : ∀ t, ξ (t+1) = ξ t+ω) (hr : ∀ t, deriv ξ t ≠ 0)
    (hinj : ∀ t h : ℝ, h ∈ Ioo (0:ℝ) 1 → ξ (t+h) ≠ ξ t)
    {G : ℂ → Fin 3 → ℝ} (hG : ∀ z ∈ closedBall (0:ℂ) 1, DifferentiableAt ℝ G z)
    (hGD : ContinuousOn (fderiv ℝ G) (closedBall 0 1))
    (hGi : ∀ z ∈ closedBall (0:ℂ) 1, Function.Injective (fderiv ℝ G z))
    (hboundary : ∀ t, F (periodTorusProjection L (ξ t)) = G (spinCircleParameter t))
    (htrans : ∀ t : unitInterval, fderiv ℝ G (spinDiskBoundary t) (I*(I*spinDiskBoundary t)) ∉
      LinearMap.range (fderiv ℝ (F ∘ periodTorusProjection L) (ξ t.1)).toLinearMap) :
    capAmbientSpinQuadratic L F (1,0) * capAmbientSpinQuadratic L F (0,1) = 0 := by
  classical
  have htest : ¬(∀ i, CapGeneratorAmbientSpinCloses L F i) := by
    intro hgen
    obtain ⟨q,hqc,hq⟩ := torus_ambient_lifts_along_essential_curve L hFD hFi hgen hξ hω hωL hp hr hinj
    let Y := F ∘ periodTorusProjection L
    let A (t : unitInterval) := fderiv ℝ Y (ξ t.1)
    let B (t : unitInterval) := fderiv ℝ G (spinDiskBoundary t)
    have hball (t : unitInterval) : spinDiskBoundary t ∈ closedBall (0:ℂ) 1 := by simp [mem_closedBall,spinDiskBoundary_norm]
    let v := fun t : unitInterval => I*spinDiskBoundary t
    have hv (t) : v t ≠ 0 := mul_ne_zero I_ne_zero (spinDiskBoundary_ne_zero t)
    let b : C(unitInterval,OrthonormalTangentPair) := ⟨fun t => spatialDifferentialFrame (hGi _ (hball t)) (hv t),
      spatialDifferentialFrame_continuous (hGD.comp_continuous spinDiskBoundary_continuous hball)
        (continuous_const.mul spinDiskBoundary_continuous) _ _⟩
    let a : C(unitInterval,OrthonormalTangentPair) :=
      ⟨fun t => unitQuaternionFrame (q t),unitQuaternionFrame_isCoveringMap.continuous.comp q.continuous⟩
    have ha (t : unitInterval) : a t = spatialDifferentialFrame (hFi (ξ t.1)) (hr t.1) := hq t
    have hbe : b 1 = b 0 := by apply Subtype.ext; simp only [b,ContinuousMap.coe_mk,spatialDifferentialFrame,v,spinDiskBoundary_endpoints]
    have hae : a 1 = a 0 := congrArg unitQuaternionFrame hqc
    have hfirst (t : unitInterval) : (a t).1.1 = (b t).1.1 := by
      let x := t.1
      have hy := (hF (ξ x)).hasFDerivAt.comp_hasDerivAt x ((hξ.differentiable (by simp) x).hasDerivAt)
      have hg := (hG (spinDiskBoundary t) (hball t)).hasFDerivAt.comp_hasDerivAt x (spinCircleParameter_hasDerivAt x)
      have he : A t (deriv ξ x) = (2*Real.pi) • (B t (v t)) := by
        have h := (hy.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => (hboundary s).symm))).unique hg
        simpa only [A,B,Y,x,v,spinCircleParameter,spinDiskBoundary,map_smul] using h
      rw [ha]
      change spatialUnitVector (A t (deriv ξ x)) = spatialUnitVector (B t (v t))
      rw [he,spatialUnitVector_pos_smul (by positivity : 0 < 2*Real.pi)]
    have hn (t : unitInterval) : (b t).1.2 ≠ -(a t).1.2 := by
      rw [ha]
      exact transverse_differential_frames_ne_opposite (hFi _) (hGi _ (hball t)) (hr t.1) (hv t)
        (by rw [← ha]; exact hfirst t) (htrans t)
    obtain ⟨l,hl,hle⟩ := common_tangent_frame_closed_lift hae hbe hfirst hn q (fun _ => rfl) hqc
    exact immersed_disk_boundary_spin_not_closed hGD hGi l (fun t => congrArg Subtype.val (hl t)) hle
  by_cases h₀ : CapGeneratorAmbientSpinCloses L F 0
  · have h₁ : ¬ CapGeneratorAmbientSpinCloses L F 1 := fun h => htest (by
        intro i; fin_cases i <;> assumption)
    simp [capAmbientSpinQuadratic,torusQuadratic,h₀,h₁]
  · simp [capAmbientSpinQuadratic,torusQuadratic,h₀]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_with_compressing_disk_even
