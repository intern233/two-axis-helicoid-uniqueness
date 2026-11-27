import TwoAxisHelicoid.MarkedMinimalFamilyContinuation
import TwoAxisHelicoid.UniformLopezRosExterior
import TwoAxisHelicoid.AnalyticLopezRosFamily
import TwoAxisHelicoid.TorusSpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The López–Ros open-and-closed argument for a marked embedded
one-handle surface with its actual exponential exterior coordinate
and one interior simple vertical point. No global flux theorem,
openness of embeddedness, or first-contact principle is assumed. -/
theorem nonvertical_flux_from_exterior_and_simple_point {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricExteriorCoordinate X)
    (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (Y : PuncturedPeriodTorus L → Fin 3 → ℝ) (eq : ∀ p, Y (f p)=X p)
    (reg : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z))
    {a : ℂ} (ha : a ∉ L.lattice) (hm : nullHorizontalMinus (torusImmersionForms L Y a) ≠ 0)
    (hz : torusImmersionForms L Y a 2=0) (hs : deriv (fun z => torusImmersionForms L Y z 2) a ≠ 0) :
    HasIntrinsicNonverticalFlux L Y := by
  by_contra vertical
  obtain ⟨Z,h1,height,dZ⟩ := vertical_flux_joint_analytic_family L Y reg vertical
  let W := fun s : ℝ => Z (Real.exp s)
  let U := fun s : ℝ => W s ∘ f
  have data (s : ℝ) (z : ℂ) (hn : z ∉ L.lattice) := dZ (Real.exp s) (Real.exp_pos s).ne' z hn
  have joint (s : ℝ) (z : ℂ) (hn : z ∉ L.lattice) :
      AnalyticAt ℝ (fun q : ℝ × ℂ => puncturedTorusPullback L (W q.1) q.2) (s,z) := by
    have e : AnalyticAt ℝ (fun q : ℝ × ℂ => (Real.exp q.1,q.2)) (s,z) :=
      ((ContinuousLinearMap.fst ℝ ℝ ℂ).analyticAt _).rexp'.prod ((ContinuousLinearMap.snd ℝ ℝ ℂ).analyticAt _)
    exact (data s z hn).1.comp (f := fun q : ℝ × ℂ => (Real.exp q.1,q.2)) e
  have cw := marked_family_joint_continuous L W (fun s z hn => (joint s z hn).continuousAt)
  have cu : Continuous (fun p : ℝ × M => U p.1 p.2) := cw.comp (f := fun p : ℝ × M => (p.1,f p.2)) (by fun_prop)
  have escape := true_exterior_height_coordinate_escapes (homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L) f)
    A.chart A.target A.core _ ((continuous_apply 2).comp closed.continuous) A.heightOffset A.height
  have dY z (hn : z ∉ L.lattice) : DifferentiableAt ℝ (puncturedTorusPullback L Y) z :=
    (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((reg z hn).1 j))).differentiableAt
  obtain ⟨r,hr,der⟩ := original_exterior_positive_deformation_derivatives f hf X hX A Y eq dY W
    (fun s z hn => (data s z hn).2.2.2.2)
  have hheight (s : ℝ) (z : ℂ) (h : r<‖z‖) : U s (A.chart.symm z) 2=z.re+A.heightOffset := by
    have htarget : z ∈ A.chart.target := A.target ▸ hr.trans h
    change Z _ (f _) 2=_
    rw [height,eq,A.height _ (A.chart.map_target htarget),A.chart.right_inv htarget,add_comm]
  have tight (s : ℝ) : ∃ K : Set (PuncturedPeriodTorus L × PuncturedPeriodTorus L), IsCompact K ∧
      ∀ᶠ q in 𝓝 s, immersionDoublePoints (W q) ⊆ K := by
    let J := Icc (s-1) (s+1)
    obtain ⟨C,hC,hb⟩ := compact_double_points_of_exponential_end_family A.chart A.target A.core escape hr U cu
      A.pitch A.heightOffset A.correction A.analytic der hheight (show IsCompact J from isCompact_Icc)
    refine ⟨(f '' C) ×ˢ (f '' C),(hC.image f.continuous).prod (hC.image f.continuous),?_⟩
    filter_upwards [show J ∈ 𝓝 s from Icc_mem_nhds (by linarith) (by linarith)] with q hq
    rintro ⟨x,y⟩ ⟨same,ne⟩
    have inside : (f.symm x,f.symm y) ∈ immersionDoublePoints (U q) := by
      refine ⟨?_,fun h => ne (f.symm.injective h)⟩
      simpa only [U,Function.comp_apply,f.apply_symm_apply] using same
    have hp := hb q hq inside
    exact ⟨⟨f.symm x,hp.1,f.apply_symm_apply x⟩,⟨f.symm y,hp.2,f.apply_symm_apply y⟩⟩
  have injY : Function.Injective Y := by
    intro x y he
    obtain ⟨p,rfl⟩ := f.surjective x
    obtain ⟨q,rfl⟩ := f.surjective y
    exact congrArg f (closed.injective ((eq p).symm.trans (he.trans (eq q))))
  have initial : Function.Injective (W 0) := by simpa only [W,Real.exp_zero,h1] using injY
  have inj := marked_minimal_family_injectivity_continuation L W joint
    (fun s z hn => ⟨(data s z hn).2.1,(data s z hn).2.2.1,(data s z hn).2.2.2.1⟩) tight initial
  have crosses := lopez_ros_torus_position_eventually_not_injective L Y (fun z hn => ⟨(reg z hn).1,(reg z hn).2.1⟩)
    ha hm hz hs Z (fun k hk z hn => (dZ k hk.ne' z hn).2.2.2.2) (V := univ) Filter.univ_mem
  obtain ⟨s,x,_,y,_,ne,same⟩ := (Real.tendsto_exp_atTop.eventually crosses).exists
  exact ne (inj s same)

/-- With the exterior and uniformization conclusions, the original
embedded one-ended genus-one surface carries a closed curve with a
nonzero horizontal spatial conormal integral. No straight-axis symmetry
or additional nonvertical-flux input is used. -/
theorem original_exterior_one_handle_has_horizontal_flux {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{u} L₀) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricExteriorCoordinate X) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ p, Y (f p)=X p) ∧ MarkedHelicoidalEndForms L Y ∧ HasIntrinsicNonverticalFlux L Y ∧
      ∃ (p : M) (γ : Path p p) (q : PuncturedPeriodTorus L) (δ : Path q q) (j : Fin 3) (v : ℝ),
      (∀ t, f (γ t)=δ t) ∧ (∀ t, Y (δ t)=X (γ t)) ∧ j ≠ 2 ∧ v ≠ 0 ∧ TorusSpatialConormalIntegral L Y j δ v := by
  obtain ⟨L,f,Y,hf,hi,eq,_,e⟩ := original_exterior_surface_marked_end_forms top uniform X closed hX A
  obtain ⟨κ,R,_,hR,log⟩ := e.gauss_expansion
  have reg := torusImmersionForms_regular L Y (fun z hz => (e.regular z hz).1) (fun z hz => (e.regular z hz).2.1)
  have nz (z : ℂ) (hz : z ∉ L.lattice) : torusImmersionForms L Y z ≠ 0 :=
    immersionComplexCoefficient_regular (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((e.regular z hz).1 j))).differentiableAt (e.regular z hz).2.2
  obtain ⟨a,b,D⟩ := one_end_torus_has_simple_gauss_divisor L _ reg.1 (torusImmersionForms_periodic L Y)
    reg.2.1 nz e.height_order hR log
  have flux := nonvertical_flux_from_exterior_and_simple_point X closed hX A L f hf Y eq e.regular
    D.zero_regular D.minus_nonzero D.height_zero D.simple_height_zero
  obtain ⟨q,δ,j,v,hj,hδ,hv⟩ := (torus_spatial_nonvertical_flux_iff L Y (fun z hz => ⟨(e.regular z hz).1,(e.regular z hz).2.1⟩)).mpr flux
  let γ := δ.map f.symm.continuous
  have proj (t : unitInterval) : f (γ t)=δ t := f.apply_symm_apply _
  exact ⟨L,f,Y,hf,hi,eq,e,flux,_,γ,q,δ,j,v,proj,fun t => (proj t) ▸ eq (γ t),hj,hv,hδ⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_exterior_one_handle_has_horizontal_flux
