import TwoAxisHelicoid.LopezRosHolomorphicCoordinates
import TwoAxisHelicoid.ExteriorWeierstrassDerivative
import TwoAxisHelicoid.MarkedExteriorGaussDivisor

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Every holomorphic chart mapping into a marked punctured torus has
a local holomorphic lift to its genuine lattice-complement plane. -/
theorem holomorphic_finite_torus_lift {L : PeriodPair} {φ : ℂ → PuncturedPeriodTorus L} {z : ℂ}
    (hp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω φ z) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v z ∧ ∀ᶠ w in 𝓝 z, ∃ h : v w ∉ L.lattice, puncturedPlaneProjection L ⟨v w,h⟩=φ w := by
  let q := (φ z).1
  let χ := chartAt ℂ q
  let φ' := fun w => (φ w).1
  have hc := (contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).contMDiffAt.comp z hp
  have a := (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ q)) (mem_chart_source ℂ q)).comp z hc
  refine ⟨χ ∘ φ',a.contDiffAt.analyticAt,?_⟩
  filter_upwards [hc.continuousAt.eventually (χ.open_source.mem_nhds (mem_chart_source ℂ q))] with w hw
  change φ' w ∈ χ.source at hw
  have proj : periodTorusProjection L (χ (φ' w))=(φ w).1 := by
    rw [← periodTorus_chart_symm_eq_projection L q]
    exact χ.left_inv hw
  exact ⟨fun h => (φ w).2 (proj.symm.trans ((periodTorusProjection_eq_zero L _).mpr h)),Subtype.ext proj⟩

theorem deformed_torus_chart_derivative {L : PeriodPair} (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    {k : ℂ} {φ : ℂ → PuncturedPeriodTorus L} {z : ℂ} (hp : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω φ z)
    (dx : ∀ u ∉ L.lattice, HasFDerivAt (puncturedTorusPullback L X) (nullRealDerivative (torusImmersionForms L X u)) u)
    (dy : ∀ u ∉ L.lattice, HasFDerivAt (puncturedTorusPullback L Y) (nullRealDerivative (lopezRosCoefficients k (torusImmersionForms L X u))) u)
    {g h : ℂ} (base : HasFDerivAt (X ∘ φ) (nullRealDerivative (weierstrassTriple g h)) z) :
    HasFDerivAt (Y ∘ φ) (nullRealDerivative (weierstrassTriple (k*g) h)) z := by
  obtain ⟨v,av,ev⟩ := holomorphic_finite_torus_lift hp
  have eq (U : PuncturedPeriodTorus L → Fin 3 → ℝ) : U ∘ φ =ᶠ[𝓝 z] puncturedTorusPullback L U ∘ v := by
    filter_upwards [ev] with w hw
    obtain ⟨hr,pr⟩ := hw
    change U (φ w)=puncturedTorusPullback L U (v w)
    simp only [puncturedTorusPullback,dite_eq_left hr,pr]
  obtain ⟨regular,_⟩ := ev.self_of_nhds
  exact lopezRos_derivative_in_holomorphic_parameter av.differentiableAt.hasDerivAt (dx _ regular) (dy _ regular) (eq X) (eq Y) base

/-- The geometric exterior coordinate of the original surface works on
one fixed exterior region simultaneously for every deformed immersion.
Its height chart and the domain cutoff do not depend on the multiplier. -/
theorem original_exterior_positive_deformation_derivatives {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {L : PeriodPair} (f : M ≃ₜ PuncturedPeriodTorus L)
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (eq : ∀ p, Y (f p)=X p) (reg : ∀ z ∉ L.lattice, DifferentiableAt ℝ (puncturedTorusPullback L Y) z)
    (W : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ)
    (dw : ∀ s z, z ∉ L.lattice → HasFDerivAt (puncturedTorusPullback L (W s))
      (nullRealDerivative (lopezRosCoefficients (Real.exp s:ℂ) (torusImmersionForms L Y z))) z) :
    ∃ r : ℝ, A.radius<r ∧ ∀ z : ℂ, r<‖z‖ → ∀ s : ℝ,
      HasFDerivAt ((W s ∘ f) ∘ A.chart.symm)
        (nullRealDerivative (weierstrassTriple ((Real.exp s:ℂ)*exp (I*A.pitch*z+A.correction z⁻¹)) 1)) z := by
  obtain ⟨d,_,hd⟩ := hasBasis_cobounded_norm.eventually_iff.mp (geometric_exterior_coordinate_weierstrass X hX A)
  let r := max d A.radius+1
  have hr : A.radius<r := by dsimp [r]; linarith [le_max_right d A.radius]
  have hd' : d<r := by dsimp [r]; linarith [le_max_left d A.radius]
  refine ⟨r,hr,?_⟩
  intro z hz s
  have he : z ∈ A.chart.target := A.target ▸ hr.trans hz
  have hf' := hf.contMDiffAt.comp z (contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic he)
  have pos : Y ∘ (f ∘ A.chart.symm)=X ∘ A.chart.symm := funext fun w => eq _
  exact deformed_torus_chart_derivative Y (W s) hf' (fun u hu => immersionComplexCoefficient_hasFDerivAt (reg u hu))
    (dw s) (pos.symm ▸ hd (hd'.trans hz).le)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_exterior_positive_deformation_derivatives
