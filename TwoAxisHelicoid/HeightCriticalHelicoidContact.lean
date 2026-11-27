import TwoAxisHelicoid.HelicoidLocalCoincidence
import TwoAxisHelicoid.ActualHeightSaddles
import TwoAxisHelicoid.ActualGlobalImmersion

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- A regular patch of a ruled helicoid has submersive height, even
when the surface parametrization is only known to be an immersion. -/
theorem helicoid_contained_germ_height_regular {X : ℂ → Fin 3 → ℝ} {z g : ℂ} {α b : ℝ}
    (hg : normSq g=1) (reg : DifferentiableAt ℝ X z) (inj : Function.Injective (fderiv ℝ X z))
    (inside : ∀ᶠ w in 𝓝 z, X w ∈ range (axisRuledHelicoid g α b)) :
    fderiv ℝ (fun w => X w 2) z ≠ 0 := by
  intro crit
  let A := fderiv ℝ X z
  let D := fun j : Fin 3 => (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp A
  have d (j : Fin 3) : HasFDerivAt (fun w => X w j) (D j) z := ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z reg.hasFDerivAt)
  have height := (d 2).fderiv.symm.trans crit
  let phase := fun h : ℝ => g*exp (I*(α*(h-b):ℝ))
  let v := phase (X z 2)
  have nz : v≠0 := mul_ne_zero (fun e => by rw [e,map_zero] at hg; exact zero_ne_one hg) (exp_ne_zero _)
  have dp : DifferentiableAt ℝ phase (X z 2) := by
    dsimp [phase]
    fun_prop
  have zeroPhase : HasFDerivAt (fun w => phase (X w 2)) (0 : ℂ →L[ℝ] ℂ) z := by
    simpa only [Function.comp_def,height,ContinuousLinearMap.comp_zero] using dp.hasFDerivAt.comp z (d 2)
  have re : HasFDerivAt (fun w => (phase (X w 2)).re) (0 : ℂ →L[ℝ] ℝ) z := by
    simpa only [Function.comp_def,reCLM_apply,ContinuousLinearMap.comp_zero] using reCLM.hasFDerivAt.comp z zeroPhase
  have im : HasFDerivAt (fun w => (phase (X w 2)).im) (0 : ℂ →L[ℝ] ℝ) z := by
    simpa only [Function.comp_def,imCLM_apply,ContinuousLinearMap.comp_zero] using imCLM.hasFDerivAt.comp z zeroPhase
  have side : HasFDerivAt (fun w => axisHelicoidSide g α b (X w)) (v.re • D 0+v.im • D 1) z := by
    simpa only [axisHelicoidSide,v,phase,Pi.add_def,Pi.mul_def,smul_zero,add_zero] using (re.mul (d 0)).add (im.mul (d 1))
  have germ : (fun w => axisHelicoidSide g α b (X w)) =ᶠ[𝓝 z] fun _ => 0 :=
    inside.mono fun _ h => (axisHelicoidSide_eq_zero_iff hg α b _).mpr h
  have s0 : v.re • D 0+v.im • D 1=0 := side.fderiv.symm.trans (germ.fderiv_eq.trans (hasFDerivAt_const (0:ℝ) z).fderiv)
  let H := (D 0).prod (D 1)
  have injective : Function.Injective H := by
    intro x y h
    apply inj
    funext j
    fin_cases j
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
    · exact (congrArg (fun B : ℂ →L[ℝ] ℝ => B x) height).trans ((congrArg (fun B : ℂ →L[ℝ] ℝ => B y) height).symm)
  have dimension : Module.finrank ℝ ℂ=Module.finrank ℝ (ℝ × ℝ) := by simp [Module.finrank_prod]
  obtain ⟨u,e⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := H.toLinearMap) dimension).mp injective (v.re,v.im)
  have x : D 0 u=v.re := congrArg Prod.fst e
  have y : D 1 u=v.im := congrArg Prod.snd e
  have cancel : v.re*(D 0 u)+v.im*(D 1 u)=0 := congrArg (fun T : ℂ →L[ℝ] ℝ => T u) s0
  rw [x,y] at cancel
  exact nz (Complex.normSq_eq_zero.mp cancel)

/-- A genuine critical height anywhere rules out local coincidence with
any comparison helicoid throughout a connected real analytic surface. -/
theorem analytic_height_critical_excludes_helicoid_germ {U : Set ℂ} (op : IsOpen U)
    (conn : IsPreconnected U) {X : ℂ → Fin 3 → ℝ} (an : AnalyticOnNhd ℝ X U)
    {p z : ℂ} (hp : p∈U) (hz : z∈U) (reg : Function.Injective (fderiv ℝ X p))
    (crit : fderiv ℝ (fun w => X w 2) p=0) {g : ℂ} (hg : normSq g=1) (α b : ℝ) :
    ¬ ∀ᶠ w in 𝓝 z, X w∈range (axisRuledHelicoid g α b) := by
  intro localImage
  let f := fun w => axisHelicoidSide g α b (X w)
  have analytic : AnalyticOnNhd ℝ f U := fun w hw => (axisHelicoidSide_analytic g α b _).comp (an w hw)
  have loc : f =ᶠ[𝓝 z] fun _ => 0 := localImage.mono fun _ h => (axisHelicoidSide_eq_zero_iff hg α b _).mpr h
  have all := analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const conn hz loc
  apply helicoid_contained_germ_height_regular (α := α) (b := b) hg (an p hp).differentiableAt reg _ crit
  filter_upwards [op.mem_nhds hp] with w hw using (axisHelicoidSide_eq_zero_iff hg α b _).mp (all hw)

/-- For the explicit closed Weierstrass data no interior patch can
agree with a comparison helicoid. This uses the actual height saddle
at the marked real divisor point and requires no global injectivity. -/
theorem actual_closed_immersion_excludes_local_helicoid {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) (v : thetaG t a=0) (h : thetaHorizontalPeriod t a=0) {z : ℂ}
    (hz : z∉(rhombicPeriodPair t ht).lattice) {g : ℂ} (hg : normSq g=1) (α b : ℝ) :
    ¬ ∀ᶠ w in 𝓝 z, actualGlobalImmersion t a c ht w∈range (axisRuledHelicoid g α b) := by
  let L := rhombicPeriodPair t ht
  let X := actualGlobalImmersion t a c ht
  have good := actual_global_conformal_harmonic_immersion ht ha hc v h
  have pos := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2] : a<2)
  have diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht := fun u hu => (good.2.2.2 u hu).1
  have crit := (actual_height_critical_iff ht ha hc diff pos).mpr (Or.inl (by simp))
  exact analytic_height_critical_excludes_helicoid_germ L.isClosed_lattice.isOpen_compl
    (marked_torus_lattice_complement_connected L).isPreconnected good.2.1 pos hz (good.2.2.2 _ pos).2.1 crit hg α b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_closed_immersion_excludes_local_helicoid
