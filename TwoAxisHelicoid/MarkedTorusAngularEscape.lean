import TwoAxisHelicoid.HelicoidTubeAngularEstimate
import TwoAxisHelicoid.RhombicClosedStripDirection
import TwoAxisHelicoid.AngularConeDerivative
import TwoAxisHelicoid.ProperTorusCoverPunctureEscape
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology

theorem axis_normalized_tube_vector {α : ℝ} (hα : α≠0) (b : ℝ) (p : Fin 3 → ℝ) :
    coordinateToTube (axisSpatialNormalization hα ![0,0,b] p)=
      ((-α*p 0,-α*p 1),α*(p 2-b)) := by
  rw [axisSpatialNormalization_apply]
  apply Prod.ext
  · apply Prod.ext
    · change (verticalRotation I (α • (verticalRotation I p-verticalRotation I ![0,0,b]))) 0= -α*p 0
      simp
    · change (verticalRotation I (α • (verticalRotation I p-verticalRotation I ![0,0,b]))) 1= -α*p 1
      simp
  · rfl

theorem axis_normalized_relative_horizontal {α : ℝ} (hα : α≠0) (b : ℝ) (p : Fin 3 → ℝ) :
    tubeRelativeHorizontal (coordinateToTube (axisSpatialNormalization hα ![0,0,b] p))=
      ((-α:ℝ):ℂ)*helicoidRelativeHorizontal α b p := by
  rw [axis_normalized_tube_vector hα,tubeRelativeHorizontal_exp]
  have e : Complex.mk (-α*p 0) (-α*p 1)=((-α:ℝ):ℂ)*spatialGraphProjection 0 1 p := by
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] <;> rfl
  change exp (((-(α*(p 2-b)):ℝ):ℂ)*I)*Complex.mk (-α*p 0) (-α*p 1)=_
  rw [e,helicoidRelativeHorizontal,Complex.ofReal_neg]
  ring

/-- The asymptotic unsigned angle estimate transfers to the original
marked immersion. In all boundary directions the derivative belongs to
the same angular cone as the nearby positions. -/
theorem marked_torus_strip_direction_im_tends_zero {t α : ℝ} (ht : 0<t) (hα : α≠0)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) (b : ℝ) (n : ℤ)
    (vertical : ∀ h : ℝ, (![0,0,h] : Fin 3 → ℝ) ∈ range (harmonicTorusImmersion hX))
    (endGraph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ harmonicTorusImmersion hX))
    {p : ℂ} (hp : p ∈ (rhombicPeriodPair t ht).lattice) :
    let P := fun w => helicoidRelativeHorizontal α b (X w)
    Tendsto (fun w => (rhombicStripDirection n P w).im)
      (𝓝[((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ] p) (𝓝 0) := by
  let L := rhombicPeriodPair t ht
  let A := axisSpatialNormalization hα ![0,0,b]
  let F := harmonicTorusImmersion hX
  let Y := coordinateToTube ∘ A ∘ F
  let T := fun w => coordinateToTube (A (X w))
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  let D := rhombicStripDirection n P
  have proper : IsProperMap Y := coordinateToTube_isProperMap (A.isProperMap.comp hE.isProperMap)
  have lift (z : ℂ) (hz : z ∉ L.lattice) :
      Y ⟨periodTorusProjection L z,fun e => hz ((periodTorusProjection_eq_zero L z).mp e)⟩=T z :=
    congrArg (fun q => coordinateToTube (A q)) (harmonicTorusImmersion_projection hX hz)
  have escape := proper_torus_cover_escapes_lattice proper lift hp
  have va (h : ℝ) : ((0,0),h) ∈ range Y := by
    obtain ⟨q,hq⟩ := vertical (h/α+b)
    refine ⟨q,?_⟩
    change coordinateToTube (axisSpatialNormalization hα ![0,0,b] (harmonicTorusImmersion hX q))=_
    rw [hq,axis_normalized_tube_vector hα]
    apply Prod.ext
    · ext <;> simp
    · change α*(h/α+b-b)=h
      field_simp
      ring
  have reg : ∀ᶠ z in 𝓝[(L.lattice : Set ℂ)ᶜ] p, z ∉ L.lattice := self_mem_nhdsWithin
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B,large⟩ := helicoid_C1_end_relative_horizontal_small proper.continuous va endGraph (ε/2) (half_pos hε)
  have point (w : ℂ) (hw : w ∉ L.lattice) (big : B≤‖T w‖) : |(P w).im|≤ε/2*‖P w‖ := by
    have h := large _ (by simpa only [lift w hw] using big : B≤‖Y ⟨periodTorusProjection L w,fun e => hw ((periodTorusProjection_eq_zero L w).mp e)⟩‖)
    rw [lift w hw] at h
    have form : tubeRelativeHorizontal (T w)=((-α:ℝ):ℂ)*P w := axis_normalized_relative_horizontal hα b _
    rw [form,Complex.im_ofReal_mul,abs_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg] at h
    apply (mul_le_mul_iff_right₀ (abs_pos.mpr hα)).mp
    simpa only [mul_left_comm (ε/2)] using h
  have grows := (tendsto_norm_atTop_iff_cobounded.mpr escape).eventually_gt_atTop B
  filter_upwards [reg,grows] with z hz big
  have cz : ContinuousAt T z := coordinateToTube.continuous.continuousAt.comp
    (A.continuous.continuousAt.comp (hX.differentiable z hz).continuousAt)
  have cone : ∀ᶠ w in 𝓝 z, |(P w).im|≤ε/2*‖P w‖ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,continuousAt_const.eventually_lt cz.norm big] with w hw h
    exact point w hw h.le
  have deriv_bound {j : ℤ} (on : z.re=j) : |(NormedSpace.normalize (fderiv ℝ P z 1)).im|≤ε/2 := by
    have jet := rhombic_axis_relative_direction ht hX hE.injective α b hz on
    exact normalized_complex_im_le_of_cone (half_pos hε).le
      (relative_horizontal_derivative_cone jet.1.differentiableAt jet.2.1 cone 1)
  have bound : |(D z).im|≤ε/2 := by
    by_cases l : z.re=n
    · simpa [D,rhombicStripDirection,l] using deriv_bound l
    by_cases r : z.re=(n:ℝ)+1
    · have on : z.re=(n+1:ℤ) := by exact_mod_cast r
      simpa [D,rhombicStripDirection,l,r] using deriv_bound on
    · simpa [D,rhombicStripDirection,l,r] using normalized_complex_im_le_of_cone (half_pos hε).le (point z hz big.le)
  simpa only [Real.dist_eq,sub_zero] using bound.trans_lt (half_lt_self hε)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_strip_direction_im_tends_zero
