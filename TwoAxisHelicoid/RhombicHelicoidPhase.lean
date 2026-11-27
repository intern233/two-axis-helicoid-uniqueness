import TwoAxisHelicoid.HelicoidAngularPhase
import TwoAxisHelicoid.RhombicAxisComponents
import TwoAxisHelicoid.RhombicPrimitivePatches
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ComplexConjugate

/-- Continuous polar coordinates on a simply connected open set, with
the radius and the lifted angle expressed as functions of the original
plane variable. -/
theorem continuous_polar_on_simply_connected_open {U : Set ℂ} (ho : IsOpen U)
    (hs : IsSimplyConnected U) {P : ℂ → ℂ} (hc : ContinuousOn P U) (hn : ∀ z ∈ U, P z ≠ 0) :
    ∃ r θ : ℂ → ℝ, ContinuousOn r U ∧ ContinuousOn θ U ∧
      ∀ z ∈ U, 0<r z ∧ (P z).re=r z*Real.cos (θ z) ∧ (P z).im=r z*Real.sin (θ z) := by
  classical
  let : SimplyConnectedSpace U := hs
  let : LocallyPathConnectedSpace U := ho.locallyPathConnectedSpace
  let f : C(U,{v : ℂ // v ≠ 0}) := ⟨fun z => ⟨P z.val,hn z.val z.property⟩,
    (continuousOn_iff_continuous_domRestrict.mp hc).subtype_mk _⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty U)
  obtain ⟨H,⟨_,he⟩,_⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f p
    (Complex.log (f p : ℂ)) (Subtype.ext (Complex.exp_log (f p).property))
  let logP := fun z : ℂ => if hz : z ∈ U then H ⟨z,hz⟩ else 0
  have hlog : ContinuousOn logP U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : U.domRestrict logP=H := by
      funext x
      exact dite_eq_left x.property
    rw [heq]
    exact H.continuous
  let r := fun z => Real.exp (logP z).re
  let θ := fun z => (logP z).im
  refine ⟨r,θ,Real.continuous_exp.comp_continuousOn (continuous_re.comp_continuousOn hlog),
    continuous_im.comp_continuousOn hlog,?_⟩
  intro z hz
  have e := congrArg Subtype.val (congrFun he (⟨z,hz⟩ : U))
  change Complex.exp (H ⟨z,hz⟩)=P z at e
  have eq : Complex.exp (logP z)=P z := by simpa only [logP,dite_eq_left hz] using e
  exact ⟨Real.exp_pos _,eq ▸ Complex.exp_re _,eq ▸ Complex.exp_im _⟩

/-- The horizontal projection has positive radius throughout either of
the two disks. Embeddedness and the vertical half-turn identify the
whole preimage of the vertical line. -/
theorem marked_torus_cell_horizontal_ne_zero {t a : ℝ} (ht : 0 < t) (ha : a = -2 ∨ a = -1)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX)) {z : ℂ} (hz : z ∈ rhombicAxisRectangle a t) :
    spatialGraphProjection 0 1 (X z) ≠ 0 := by
  let L := rhombicPeriodPair t ht
  have hn : z ∉ L.lattice := rhombic_horizontal_strip_not_mem ht hz.2
  have hc : conj z ∉ L.lattice := fun h => hn (by simpa using rhombic_conj_mem ht h)
  have hm : -conj z ∉ L.lattice := fun h => hc (by simpa using L.lattice.neg_mem h)
  have off : rhombicVerticalReflection ht (periodTorusProjection L z) ≠ periodTorusProjection L z := by
    apply ((rhombic_off_axes_iff_rectangle ht _).mpr ?_).2
    rcases ha with rfl | rfl
    · exact Or.inl ⟨z,hz,rfl⟩
    · exact Or.inr ⟨z,hz,rfl⟩
  intro zero
  have e₀ : X z 0=0 := congrArg re zero
  have e₁ : X z 1=0 := congrArg im zero
  have e : X (-conj z)=X z := by
    rw [hX.neg _ hc,hX.conjugation z hn]
    ext i
    fin_cases i <;> simp [e₀,e₁]
  exact off (congrArg Subtype.val (hi ((harmonicTorusImmersion_projection hX hm).trans
    (e.trans (harmonicTorusImmersion_projection hX hn).symm))))

/-- Both actual disk components admit a single-valued helicoidal phase.
For each pitch and height origin its level takes values on both sides
of every interior value in every sufficiently small neighborhood. -/
theorem marked_torus_disk_angular_phase {t a : ℝ} (ht : 0 < t) (ha : a = -2 ∨ a = -1)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) :
    let U := rhombicAxisRectangle a t
    ∃ r θ : ℂ → ℝ, ContinuousOn r U ∧ ContinuousOn θ U ∧
      (∀ z ∈ U, 0<r z ∧ X z 0=r z*Real.cos (θ z) ∧ X z 1=r z*Real.sin (θ z)) ∧
      ∀ (α b : ℝ) z, z ∈ U → ¬ IsLocalExtr (fun w => θ w-α*(X w 2-b)) z := by
  let U := rhombicAxisRectangle a t
  let : ContractibleSpace U := rhombicAxisRectangle_contractible a ht
  have ho : IsOpen U := rhombicAxisRectangle_open _ _
  have regular {z : ℂ} (hz : z ∈ U) := rhombic_horizontal_strip_not_mem ht (z := z) hz.2
  have cp : ContinuousOn (fun z => spatialGraphProjection 0 1 (X z)) U := fun z hz =>
    ((spatialGraphProjection 0 1).continuous.continuousAt.comp (hX.differentiable z (regular hz)).continuousAt).continuousWithinAt
  obtain ⟨r,θ,cr,ct,polar⟩ := continuous_polar_on_simply_connected_open ho
    (inferInstanceAs (SimplyConnectedSpace U)) cp (fun _ hz => marked_torus_cell_horizontal_ne_zero ht ha hX hE.injective hz)
  refine ⟨r,θ,cr,ct,polar,fun α b z hz => ?_⟩
  exact marked_torus_phase_no_interior_extremum hX hE (regular hz) ((ct z hz).continuousAt (ho.mem_nhds hz))
    α b (Filter.mem_of_superset (ho.mem_nhds hz) (fun w hw => polar w hw))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.continuous_polar_on_simply_connected_open
#print axioms TwoAxisHelicoid.marked_torus_disk_angular_phase
