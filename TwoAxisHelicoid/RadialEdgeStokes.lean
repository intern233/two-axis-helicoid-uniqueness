import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval

/-- Integral over an oriented side of a dilated polygon. -/
noncomputable def dilatedEdgeIntegral (f : ℂ → ℂ) (a b : ℂ) (r : ℝ) : ℂ :=
  ∫ s : ℝ in 0..1, (r:ℂ)*(b-a)*f ((r:ℂ)*(a+(s:ℂ)*(b-a)))

noncomputable def radialConnectorIntegral (f : ℂ → ℂ) (a : ℂ) (r R : ℝ) : ℂ :=
  ∫ t : ℝ in r..R, a*f ((t:ℂ)*a)

/-- Green's formula on the swept side. Holomorphy is only required on the
swept region, so the polygon may enclose an essential singularity. -/
theorem dilated_edge_stokes {f : ℂ → ℂ} (a b : ℂ) {r R : ℝ} (hr : r ≤ R)
    (hf : ∀ t ∈ Icc r R, ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f ((t:ℂ)*(a+(s:ℂ)*(b-a)))) :
    dilatedEdgeIntegral f a b R-dilatedEdgeIntegral f a b r =
      radialConnectorIntegral f b r R-radialConnectorIntegral f a r R := by
  let D := b-a
  let T := ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let S := ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let V := fun p : ℝ × ℝ => a+S p*D
  let Z := fun p : ℝ × ℝ => T p*V p
  let V' := D • S
  let Z' := fun p : ℝ × ℝ => T p • V'+V p • T
  let W := fun p : ℝ × ℝ => f (Z p)
  let W' := fun p : ℝ × ℝ => (deriv f (Z p)) • Z' p
  have vder (p) : HasFDerivAt V V' p := (S.hasFDerivAt.mul_const D).const_add a
  have zder (p) : HasFDerivAt Z (Z' p) p := T.hasFDerivAt.mul (vder p)
  let area := Icc r R ×ˢ Icc (0:ℝ) 1
  have wder (p) (hp : p ∈ area) : HasFDerivAt W (W' p) p := by
    have h := (((hf p.1 hp.1 p.2 hp.2).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp p (zder p))
    have eq : W' p = ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f (Z p))).restrictScalars ℝ).comp (Z' p) := by
      apply ContinuousLinearMap.ext
      intro v
      change deriv f (Z p) * Z' p v = Z' p v * deriv f (Z p)
      exact mul_comm _ _
    rw [eq]
    exact h
  let F := fun p : ℝ × ℝ => T p*D*W p
  let G := fun p : ℝ × ℝ => -(V p*W p)
  let F' := fun p : ℝ × ℝ => (T p*D) • W' p+W p • (D • T)
  let G' := fun p : ℝ × ℝ => -(V p • W' p + W p • V')
  have fd (p) (hp : p ∈ area) : HasFDerivAt F (F' p) p := (T.hasFDerivAt.mul_const D).mul (wder p hp)
  have gd (p) (hp : p ∈ area) : HasFDerivAt G (G' p) p := ((vder p).mul (wder p hp)).neg
  have zero (p : ℝ × ℝ) : F' p (1,0)+G' p (0,1) = 0 := by
    simp [F',G',W',Z',V',T,S,smul_eq_mul]
    ring
  have h := integral2_divergence_prod_of_hasFDerivAt F G F' G' r 0 R 1
  rw [uIcc_of_le hr,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),min_eq_left hr,max_eq_right hr] at h
  rw [min_eq_left (show (0:ℝ) ≤ 1 by norm_num),max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] at h
  have interior {p : ℝ × ℝ} (hp : p ∈ Ioo r R ×ˢ Ioo (0:ℝ) 1) : p ∈ area :=
    ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩
  specialize h (fun p hp => (fd p hp).continuousAt.continuousWithinAt)
    (fun p hp => (gd p hp).continuousAt.continuousWithinAt)
    (fun p hp => fd p (interior hp)) (fun p hp => gd p (interior hp)) (by simp [zero])
  simp only [zero,intervalIntegral.integral_zero] at h
  change dilatedEdgeIntegral f a b R-dilatedEdgeIntegral f a b r = _
  simp [F,G,W,Z,V,S,T,D,dilatedEdgeIntegral,radialConnectorIntegral,intervalIntegral.integral_neg] at h ⊢
  linear_combination -h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dilated_edge_stokes
