import TwoAxisHelicoid.OpenCoreChartParameters
import TwoAxisHelicoid.SmoothOriginalCoreLoops

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff Manifold

/-- An operator field converging locally uniformly may be evaluated
on a continuous moving tangent vector on each compact subinterval. -/
theorem local_uniform_operator_values {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set ℝ}
    {D : ℕ → ℝ → E →L[ℝ] F} {d : ℝ → E →L[ℝ] F} (conv : TendstoLocallyUniformlyOn D d atTop U)
    {v : ℝ → E} (vel : ContinuousOn v U) :
    TendstoLocallyUniformlyOn (fun n t => D n t (v t)) (fun t => d t (v t)) atTop U := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε ep t ht
  let B := ‖v t‖+1
  have bp : 0<B := by dsimp [B]; positivity
  obtain ⟨T,near,uniform⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp conv (ε/B) (div_pos ep bp) t ht
  have bound : ∀ᶠ w in 𝓝[U] t, ‖v w‖<B := (vel t ht).norm.eventually_lt_const (by dsimp [B]; linarith)
  refine ⟨T∩{x | ‖v x‖<B},inter_mem near bound,?_⟩
  filter_upwards [uniform] with n hn y hy
  have diff := hn y hy.1
  rw [dist_eq_norm] at diff ⊢
  have est := (d y-D n y).le_opNorm (v y)
  have nb : ‖v y‖≤B := le_of_lt hy.2
  calc
    _ ≤ ‖d y-D n y‖*‖v y‖ := est
    _ ≤ ‖d y-D n y‖*B := mul_le_mul_of_nonneg_left nb (norm_nonneg _)
    _ < ε := (lt_div_iff₀ bp).mp diff

/-- Graph convergence in all regular surface charts gives uniform
velocity convergence on a single fixed compact loop. Its topological
marking need not be differentiable. -/
theorem unmarked_core_curve_velocities (s : OriginalSmoothHelicoid) {V : Set s.carrier}
    (b : V) (F : ℕ → V → SurfaceEuclideanSpace)
    (input : ∀ a : OpenPartialHomeomorph s.carrier ℂ, RegularImmersionChart s.position a →
      let R := coreChartRegion V a
      let f := fun n => F n ∘ coreChartParameter V b a
      (∀ n z, z∈R → ContDiffAt ℝ 1 (f n) z) ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (f n)) (fderiv ℝ (s.euclideanPosition ∘ a.symm)) atTop R)
    (g : ℝ → V) (cg : Continuous g) (sg : ContDiff ℝ 1 (s.euclideanPosition ∘ Subtype.val ∘ g)) :
    (∀ n, ContDiff ℝ 1 (F n ∘ g)) ∧
      TendstoUniformlyOn (fun n => deriv (F n ∘ g)) (deriv (s.euclideanPosition ∘ Subtype.val ∘ g)) atTop (Icc 0 1) := by
  let p := (Subtype.val : V → s.carrier) ∘ g
  have cp : Continuous p := continuous_subtype_val.comp cg
  let X := s.euclideanPosition ∘ p
  have localData (t : ℝ) : ∃ T : Set ℝ, IsOpen T ∧ t∈T ∧ (∀ n w, w∈T → ContDiffAt ℝ 1 (F n ∘ g) w) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F n ∘ g)) (deriv X) atTop T := by
    let a := chartAt ℂ (p t)
    let R := coreChartRegion V a
    let T := p ⁻¹' a.source
    let u := a ∘ p
    let param := coreChartParameter V b a
    let fi := fun n => F n ∘ param
    let Y := s.euclideanPosition ∘ a.symm
    have op : IsOpen T := a.open_source.preimage cp
    have inc : MapsTo u T R := by
      intro w hw
      refine ⟨a.map_source hw,?_⟩
      change a.symm (a (p w))∈V
      rw [a.left_inv hw]
      exact (g w).2
    have reg := smooth_surface_regular_manifold_chart s.smooth s.immersion (p t)
    have us (w : ℝ) (hw : w∈T) : ContDiffAt ℝ 1 u w :=
      regular_immersion_curve_coordinate_C1 cp.continuousAt sg.contDiffAt a reg hw
    have idp (w : ℝ) (hw : w∈T) : param (u w)=g w :=
      Subtype.ext ((coreChartParameter_val b a (inc hw)).trans (a.left_inv hw))
    have germ (n : ℕ) (w : ℝ) (hw : w∈T) : F n ∘ g=ᶠ[𝓝 w] fi n ∘ u :=
      Filter.mem_of_superset (op.mem_nhds hw) (fun v hv => congrArg (F n) (idp v hv).symm)
    have rgerm (w : ℝ) (hw : w∈T) : X=ᶠ[𝓝 w] Y ∘ u :=
      Filter.mem_of_superset (op.mem_nhds hw) (fun v hv => congrArg s.euclideanPosition (a.left_inv hv).symm)
    obtain ⟨sm,con⟩ := input a reg
    have dr (w : ℝ) (hw : w∈T) : DifferentiableAt ℝ Y (u w) :=
      coordinateToEuclidean.differentiableAt.comp _ ((reg _ (inc hw).1).1.differentiableAt (by simp))
    have uc : ContinuousOn u T := fun w hw => (us w hw).continuousAt.continuousWithinAt
    have su : ContDiffOn ℝ 1 u T := fun w hw => (us w hw).contDiffWithinAt
    have vv : ContinuousOn (deriv u) T := su.continuousOn_deriv_of_isOpen op le_rfl
    have clim := local_uniform_operator_values (con.comp u inc uc) vv
    refine ⟨T,op,mem_chart_source ℂ _,fun n w hw => ((sm n _ (inc hw)).comp w (us w hw)).congr_of_eventuallyEq (germ n w hw),?_⟩
    apply (clim.congr (fun n w hw => ?_)).congr_right (fun w hw => ?_)
    · exact ((((sm n _ (inc hw)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt w
        ((us w hw).differentiableAt one_ne_zero).hasDerivAt).deriv).symm.trans (germ n w hw).deriv_eq.symm
    · exact (((dr w hw).hasFDerivAt.comp_hasDerivAt w ((us w hw).differentiableAt one_ne_zero).hasDerivAt).deriv).symm.trans
        (rgerm w hw).deriv_eq.symm
  constructor
  · intro n
    apply contDiff_iff_contDiffAt.mpr
    intro t
    obtain ⟨_,_,inside,sm,_⟩ := localData t
    exact sm n t inside
  · apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    intro entourage ent t ht
    obtain ⟨T,op,inside,_,conv⟩ := localData t
    obtain ⟨W,near,uniform⟩ := conv entourage ent t inside
    rw [op.nhdsWithin_eq inside] at near
    exact ⟨W,mem_nhdsWithin_of_mem_nhds near,uniform⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_uniform_operator_values
#print axioms TwoAxisHelicoid.unmarked_core_curve_velocities
