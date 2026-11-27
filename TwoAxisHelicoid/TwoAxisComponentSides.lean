import TwoAxisHelicoid.RhombicAxisComponents
import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.AxisHelicoidCalibration

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

private theorem cell_regular {t a : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ rhombicAxisRectangle a t) :
    z ∉ (rhombicPeriodPair t ht).lattice := by
  intro h
  obtain ⟨m,n,_,hi⟩ := (rhombic_mem_lattice_iff ht z).mp h
  have hp : (0 : ℝ) < n := pos_of_mul_pos_left (hi ▸ hz.2.1) ht.le
  have hl : (n : ℝ) < 1 := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_right h ht.le,hz.2.2]
  have hn : (0 : ℤ) < n := by exact_mod_cast hp
  have hm : n < (1 : ℤ) := by exact_mod_cast hl
  omega

private def cellPartner (z : ℂ) := -conj z - 2

private theorem cellPartner_mem {t a b : ℝ} (hab : a+b = -3) {z : ℂ}
    (hz : z ∈ rhombicAxisRectangle a t) : cellPartner z ∈ rhombicAxisRectangle b t := by
  have hr : (cellPartner z).re = -z.re-2 := by simp [cellPartner]
  have hi : (cellPartner z).im = z.im := by simp [cellPartner]
  exact ⟨⟨by rw [hr]; linarith [hz.1.2],by rw [hr]; linarith [hz.1.1]⟩,by change (cellPartner z).im ∈ Ioo 0 t; rw [hi]; exact hz.2⟩

private theorem cellPartner_twice (z : ℂ) : cellPartner (cellPartner z) = z := by
  norm_num [cellPartner,map_ofNat]

/-- The two open disks of the punctured rhombic torus have congruent
spatial images. Their actual parameter identification is the half-turn
around the vertical axis followed by a lattice translation. -/
theorem two_axis_component_half_turn {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) :
    let V := fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]
    V '' (X '' rhombicAxisRectangle (-2) t) = X '' rhombicAxisRectangle (-1) t := by
  let L := rhombicPeriodPair t ht
  have turn {a : ℝ} {z : ℂ} (hz : z ∈ rhombicAxisRectangle a t) :
      X (cellPartner z) = ![-X z 0,-X z 1,X z 2] := by
    have hn := cell_regular ht hz
    have hc : conj z ∉ L.lattice := fun h => hn (by simpa using rhombic_conj_mem ht h)
    have hm : -conj z ∉ L.lattice := fun h => hc (by simpa using L.lattice.neg_mem h)
    change X (-conj z + (-2)) = _
    rw [hX.periodic _ hm (-2) (L.lattice.neg_mem L.ω₁_mem_lattice),hX.neg _ hc,hX.conjugation z hn]
    simp
  apply Set.Subset.antisymm
  · rintro p ⟨_,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨_,cellPartner_mem (by norm_num : (-2:ℝ)+(-1) = -3) hz,turn hz⟩
  · rintro p ⟨z,hz,rfl⟩
    have hw := cellPartner_mem (by norm_num : (-1:ℝ)+(-2) = -3) hz
    refine ⟨_,⟨_,hw,rfl⟩,?_⟩
    change ![-X (cellPartner z) 0,-X (cellPartner z) 1,X (cellPartner z) 2] = X z
    rw [← turn hw,cellPartner_twice]

/-- The axis-only intersection with the normalized asymptotic helicoid
places the two congruent components strictly on opposite sides. -/
theorem two_axis_components_on_opposite_sides {t α : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX))
    (hinter : ∀ z ∉ (rhombicPeriodPair t ht).lattice, X z ∈ range (axisRuledHelicoid I α 0) →
      (X z 1 = 0 ∧ X z 2 = 0) ∨ (X z 0 = 0 ∧ X z 1 = 0)) :
    let A := X '' rhombicAxisRectangle (-2) t
    let B := X '' rhombicAxisRectangle (-1) t
    let s := axisHelicoidSide I α 0
    (A ⊆ {p | 0 < s p} ∧ B ⊆ {p | s p < 0}) ∨ (A ⊆ {p | s p < 0} ∧ B ⊆ {p | 0 < s p}) := by
  let L := rhombicPeriodPair t ht
  let A := rhombicAxisRectangle (-2) t
  let f := fun z => axisHelicoidSide I α 0 (X z)
  have quot {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (e : X z = X w) :
      periodTorusProjection L z = periodTorusProjection L w :=
    congrArg Subtype.val (hi ((harmonicTorusImmersion_projection hX hz).trans
      (e.trans (harmonicTorusImmersion_projection hX hw).symm)))
  have nz (z : ℂ) (hz : z ∈ A) : f z ≠ 0 := by
    intro he
    have hn := cell_regular ht hz
    have ha := hinter z hn ((axisHelicoidSide_eq_zero_iff (by simp : normSq I = 1) α 0 _).mp he)
    have off := (rhombic_off_axes_iff_rectangle ht _).mpr (Or.inl ⟨z,hz,rfl⟩)
    have hc : conj z ∉ L.lattice := fun h => hn (by simpa using rhombic_conj_mem ht h)
    rcases ha with ⟨h1,h2⟩ | ⟨h0,h1⟩
    · apply off.1
      apply quot hc hn
      rw [hX.conjugation z hn]
      ext j
      fin_cases j <;> simp [h1,h2]
    · apply off.2
      have hm : -conj z ∉ L.lattice := fun h => hc (by simpa using L.lattice.neg_mem h)
      apply quot hm hn
      rw [hX.neg _ hc,hX.conjugation z hn]
      ext j
      fin_cases j <;> simp [h0,h1]
  have cont : ContinuousOn f A := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    exact (show Continuous (axisHelicoidSide I α 0) by unfold axisHelicoidSide; fun_prop).continuousAt.comp
      (hX.differentiable z (cell_regular ht hz)).continuousAt
  let : ContractibleSpace A := rhombicAxisRectangle_contractible (-2) ht
  have conn : IsPreconnected A := isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have sign : (∀ z ∈ A, 0 < f z) ∨ ∀ z ∈ A, f z < 0 := by
    by_cases h : ∀ z ∈ A, 0 < f z
    · exact Or.inl h
    push Not at h
    obtain ⟨x,hx,hn⟩ := h
    refine Or.inr fun y hy => ?_
    by_contra! hp
    obtain ⟨v,hv,ev⟩ := conn.intermediate_value hx hy cont (show (0:ℝ) ∈ Icc (f x) (f y) from ⟨hn,hp⟩)
    exact nz v hv ev
  let V := fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]
  have e : V '' (X '' A) = X '' rhombicAxisRectangle (-1) t := two_axis_component_half_turn ht hX
  have v (p : Fin 3 → ℝ) : axisHelicoidSide I α 0 (V p) = -axisHelicoidSide I α 0 p := by
    simp [axisHelicoidSide,V]
    ring
  rcases sign with h | h
  · left
    refine ⟨fun _ ⟨z,hz,he⟩ => he ▸ h z hz,?_⟩
    rw [← e]
    rintro p ⟨_,⟨z,hz,rfl⟩,rfl⟩
    change axisHelicoidSide I α 0 (V (X z)) < 0
    rw [v]
    exact neg_neg_of_pos (h z hz)
  · right
    refine ⟨fun _ ⟨z,hz,he⟩ => he ▸ h z hz,?_⟩
    rw [← e]
    rintro p ⟨_,⟨z,hz,rfl⟩,rfl⟩
    change 0 < axisHelicoidSide I α 0 (V (X z))
    rw [v]
    exact neg_pos.mpr (h z hz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_axis_components_on_opposite_sides
