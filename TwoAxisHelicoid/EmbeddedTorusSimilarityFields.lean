import TwoAxisHelicoid.EmbeddedAmbientFlow
import TwoAxisHelicoid.SimilarityFlowMetric
import TwoAxisHelicoid.SimilarityNormalTangency
import TwoAxisHelicoid.TangentOrbitInvariance
import TwoAxisHelicoid.SpatialSimilarityTorusSquare

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology

/-- The seven normal components of infinitesimal similarities are independent
on any closed embedded regular conformal analytic once-punctured torus.
A tangent affine velocity is integrated on the actual surface; finiteness
of punctured torus automorphisms makes its entire spatial flow trivial. -/
theorem embedded_torus_similarity_normal_independent (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hY : ∀ z ∉ L.lattice, AnalyticAt ℝ (X ∘ periodTorusProjection L) z ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (a b : Fin 3 → ℝ) (d : ℝ) (hzero : ∀ z ∉ L.lattice,
      similarityNormal (X ∘ periodTorusProjection L) (harmonicChartNormal (X ∘ periodTorusProjection L)) a b d z = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  let U := (L.lattice : Set ℂ)ᶜ
  let Y := X ∘ periodTorusProjection L
  let Z := fun q : PuncturedPeriodTorus L => X q.1
  let P := similarityLinear b d
  let V := fun p => a+P p
  let F := affineAmbientFlow P a
  have hopen : IsOpen U := L.isClosed_lattice.isOpen_compl
  have him : Y '' U = range Z := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨puncturedPlaneProjection L ⟨z,hz⟩,rfl⟩
    · rintro ⟨q,rfl⟩
      obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
      exact ⟨z.1,z.2,rfl⟩
  have hV : ∀ p, AnalyticAt ℝ V p := fun p => analyticAt_const.add (P.analyticAt p)
  have hlip : LipschitzWith ‖P‖₊ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (a+P x) (a+P y) ≤ _
    rw [dist_add_left]
    exact P.lipschitzWith.dist_le_mul x y
  have htan (z : ℂ) (hz : z ∈ U) : ∃ w : ℂ, fderiv ℝ Y z w = V (Y z) := by
    obtain ⟨w,hw⟩ := similarity_normal_zero_is_tangent (hY z hz).1 (hY z hz).2.1 (hY z hz).2.2 a b d (hzero z hz)
    exact ⟨w,by simpa only [similarityField,V,P,similarityLinear_apply,add_assoc] using hw⟩
  have hin (s : ℝ) (q : PuncturedPeriodTorus L) : F s (Z q) ∈ range Z := by
    have h0 : F 0 (Z q) ∈ Y '' U := by rw [him,show F 0 (Z q) = Z q from affineAmbientFlow_zero _ _ _]; exact mem_range_self q
    rw [← him]
    exact tangent_ambient_orbit_in_closed_image hopen (him.symm ▸ hX.isClosed_range)
      (fun z hz => ⟨(hY z hz).1,(hY z hz).2.2⟩) hV hlip htan (affineAmbientFlow_deriv P a (Z q)) h0 s
  obtain ⟨g,he,hg,hadd,hgid,hinv⟩ := embedded_ambient_flow_action hX.isEmbedding P a hin
  have hsq (t : ℝ) : PuncturedTorusHolomorphic L L ((g t).trans (g t)) := by
    apply spatial_similarity_torus_square_holomorphic L X hY (F t) _ (fun p => affineAmbientFlow_hasFDerivAt P a p t)
      (Real.exp_pos (2*d*t)) (similarity_flow_metric a b d t) (g t) (he t)
    intro p
    have h : F t = fun v => affineAmbientLinearPart P a t v+F t 0 := funext fun v => affineAmbientFlow_linear_part _ _ _ _
    rw [h]
    exact ((affineAmbientLinearPart P a t).analyticAt _).add analyticAt_const
  have hh (t : ℝ) : PuncturedTorusHolomorphic L L (g t) := by
    have ht : g t = (g (t/2)).trans (g (t/2)) := by
      apply Homeomorph.ext
      intro q
      exact (congrArg (fun s => g s q) (show t = t/2+t/2 by ring)).trans (hadd _ _ _)
    rw [ht]
    exact hsq _
  have hi (t : ℝ) : PuncturedTorusHolomorphic L L (g t).symm := by
    have ht : (g t).symm = g (-t) := Homeomorph.ext (hinv t)
    rw [ht]
    exact hh _
  have hpoint (t : ℝ) (q : PuncturedPeriodTorus L) : F t (Z q) = Z q := by
    calc
      F t (Z q) = Z (g t q) := (he t q).symm
      _ = Z (g 0 q) := congrArg Z (continuous_punctured_torus_automorphisms_constant L g hh hi hg t 0 q)
      _ = Z q := congrArg Z (hgid q)
  have hv (q : PuncturedPeriodTorus L) : similarityField a b d (Z q) = 0 := by
    have hz := (affineAmbientFlow_deriv P a (Z q) 0).unique
      ((hasDerivAt_const (0:ℝ) (Z q)).congr_of_eventuallyEq (Eventually.of_forall fun t => hpoint t q))
    simpa only [affineAmbientFlow_zero,similarityField,P,similarityLinear_apply,add_assoc] using hz
  let w := L.ω₁/2
  have hw : w ∈ U := L.ω₁_div_two_notMem_lattice
  apply similarityField_zero_near_immersion (hY w hw).1.differentiableAt.hasFDerivAt (hY w hw).2.2
  filter_upwards [hopen.mem_nhds hw] with z hz
  exact hv (puncturedPlaneProjection L ⟨z,hz⟩)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_torus_similarity_normal_independent
