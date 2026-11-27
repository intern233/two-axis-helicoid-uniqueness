import TwoAxisHelicoid.FixedAxesJacobiDilation
import TwoAxisHelicoid.CoordinateSignMaps

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ComplexConjugate

private theorem velocity_of_reflected_curve {f g : ℝ → Fin 3 → ℝ} {u v : Fin 3 → ℝ}
    (hf : HasDerivAt f u 0) (hg : HasDerivAt g v 0) (T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (he : ∀ᶠ s in 𝓝 (0:ℝ), g s = T (f s)) : v = T u :=
  hg.unique ((T.hasFDerivAt.comp_hasDerivAt 0 hf).congr_of_eventuallyEq he)

/-- Differentiate the two actual position symmetries in a fixed-axis family.
Its normal velocity is odd in both reflections and vanishes on their axes. -/
theorem fixed_axes_family_normal_velocity_odd (L : PeriodPair) (hL : ConjugationInvariantLattice L)
    (F : ℝ → ℂ → Fin 3 → ℝ) (V : ℂ → Fin 3 → ℝ)
    (hX : TwoAxisHarmonicConformalImmersion L (F 0))
    (hv : ∀ z ∉ L.lattice, HasDerivAt (fun s => F s z) (V z) 0)
    (hs : ∀ z ∉ L.lattice, ∀ᶠ s in 𝓝 (0:ℝ), F s (conj z) = halfTurnX (F s z) ∧
      F s (-conj z) = halfTurnZ (F s z)) :
    let u := fun z => V z ⬝ᵥ harmonicChartNormal (F 0) z
    ∀ z ∉ L.lattice, u (conj z) = -u z ∧ u (-conj z) = -u z ∧
      (conj z = z ∨ -conj z = z → u z = 0) := by
  let A := coordinateSignMap (![1,-1,-1] : Fin 3 → ℝ)
  let B := coordinateSignMap (![-1,-1,1] : Fin 3 → ℝ)
  have hA (v : Fin 3 → ℝ) : A v = halfTurnX v := by ext j; fin_cases j <;> simp [A,halfTurnX]
  have hB (v : Fin 3 → ℝ) : B v = halfTurnZ v := by ext j; fin_cases j <;> simp [B,halfTurnZ]
  intro _ z hz
  have hc : conj z ∉ L.lattice := fun h => hz (by simpa using hL (conj z) h)
  have hn : -conj z ∉ L.lattice := by simpa using hc
  have vx := (velocity_of_reflected_curve (hv z hz) (hv _ hc) A
    ((hs z hz).mono fun s h => h.1.trans (hA _).symm)).trans (hA _)
  have vz := (velocity_of_reflected_curve (hv z hz) (hv _ hn) B
    ((hs z hz).mono fun s h => h.2.trans (hB _).symm)).trans (hB _)
  obtain ⟨nx,nz⟩ := harmonic_axis_oriented_normals hL hX hz
  let u := fun x => V x ⬝ᵥ harmonicChartNormal (F 0) x
  have hx : u (conj z) = -u z := by
    dsimp only [u]
    rw [vx,nx]
    simp [halfTurnX,dotProduct,Fin.sum_univ_succ]
  have hz' : u (-conj z) = -u z := by
    dsimp only [u]
    rw [vz,nz]
    simp [halfTurnZ,dotProduct,Fin.sum_univ_succ]
  refine ⟨hx,hz',?_⟩
  rintro (h | h)
  · rw [h] at hx; change u z = 0; linarith
  · rw [h] at hz'; change u z = 0; linarith

/-- For a differentiable equivariant family, even a velocity agreeing with
an ambient similarity only in its normal component must vanish in all seven
similarity directions when the two axes and the nonzero pitch stay fixed. -/
theorem fixed_axes_family_has_no_similarity_normal_velocity (L : PeriodPair) (hL : ConjugationInvariantLattice L)
    (X : PeriodTorus L → Fin 3 → ℝ) (hc : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (F : ℝ → ℂ → Fin 3 → ℝ) (V : ℂ → Fin 3 → ℝ) (h0 : F 0 = X ∘ periodTorusProjection L)
    (hX : TwoAxisHarmonicConformalImmersion L (F 0))
    (hv : ∀ z ∉ L.lattice, HasDerivAt (fun s => F s z) (V z) 0)
    (hs : ∀ z ∉ L.lattice, ∀ᶠ s in 𝓝 (0:ℝ), F s (conj z) = halfTurnX (F s z) ∧ F s (-conj z) = halfTurnZ (F s z))
    (a b : Fin 3 → ℝ) (d pitch : ℝ) (hp : pitch ≠ 0)
    (hfix : ∀ᶠ s in 𝓝 (0:ℝ), Real.exp (s*d)*pitch = pitch)
    (hvel : ∀ z ∉ L.lattice, V z ⬝ᵥ harmonicChartNormal (F 0) z =
      similarityNormal (F 0) (harmonicChartNormal (F 0)) a b d z) : a = 0 ∧ b = 0 ∧ d = 0 := by
  have h := fixed_axes_family_normal_velocity_odd L hL F V hX hv hs
  apply fixed_axes_and_pitch_remove_similarity_fields L hL X hc (h0 ▸ hX) a b d pitch hp hfix
  · intro z hz
    have hcz : conj z ∉ L.lattice := fun hm => hz (by simpa using hL (conj z) hm)
    change similarityNormal _ _ _ _ _ _ = -similarityNormal _ _ _ _ _ _
    rw [← h0,← hvel _ hcz,← hvel _ hz]
    exact (h z hz).1
  · intro z hz
    have hcz : conj z ∉ L.lattice := fun hm => hz (by simpa using hL (conj z) hm)
    have hn : -conj z ∉ L.lattice := by simpa using hcz
    change similarityNormal _ _ _ _ _ _ = -similarityNormal _ _ _ _ _ _
    rw [← h0,← hvel _ hn,← hvel _ hz]
    exact (h z hz).2.1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_axes_family_has_no_similarity_normal_velocity
