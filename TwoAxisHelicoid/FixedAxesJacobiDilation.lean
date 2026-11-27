import TwoAxisHelicoid.HarmonicAxisNormals
import TwoAxisHelicoid.EmbeddedTorusSimilarityFields

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology ComplexConjugate

/-- The two fixed axes remove translation and rotation, and local constancy
of the actual pitch of the dilation group removes its remaining velocity.
The normal and all seven fields are computed from the same position map. -/
theorem fixed_axes_and_pitch_remove_similarity_fields (L : PeriodPair) (hL : ConjugationInvariantLattice L)
    (X : PeriodTorus L → Fin 3 → ℝ) (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hY : TwoAxisHarmonicConformalImmersion L (X ∘ periodTorusProjection L))
    (a b : Fin 3 → ℝ) (d pitch : ℝ) (hp : pitch ≠ 0)
    (hfix : ∀ᶠ s : ℝ in 𝓝 0, Real.exp (s*d)*pitch = pitch)
    (hoddX : ∀ z ∉ L.lattice, let Y := X ∘ periodTorusProjection L
      similarityNormal Y (harmonicChartNormal Y) a b d (conj z) = -similarityNormal Y (harmonicChartNormal Y) a b d z)
    (hoddZ : ∀ z ∉ L.lattice, let Y := X ∘ periodTorusProjection L
      similarityNormal Y (harmonicChartNormal Y) a b d (-conj z) = -similarityNormal Y (harmonicChartNormal Y) a b d z) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  let U := (L.lattice : Set ℂ)ᶜ
  let Y := X ∘ periodTorusProjection L
  let P := fun z : U => Y z
  let N := fun z : U => harmonicChartNormal Y z
  have conj_reg {z : ℂ} (hz : z ∉ L.lattice) : conj z ∉ L.lattice := fun hm => hz (by simpa using hL (conj z) hm)
  let rx := fun z : U => (⟨conj z.1,conj_reg z.2⟩ : U)
  let rz := fun z : U => (⟨-conj z.1,by change -conj z.1 ∉ L.lattice; simpa using conj_reg z.2⟩ : U)
  have hx (z : U) : P (rx z) = halfTurnX (P z) := hY.conjugation z.1 z.2
  have hv (z : U) : P (rz z) = halfTurnZ (P z) := by
    change Y (-conj z.1) = _
    have hn : Y (-conj z.1) = ![-Y (conj z.1) 0,Y (conj z.1) 1,-Y (conj z.1) 2] := hY.neg _ (conj_reg z.2)
    rw [hn]
    have he : Y (conj z.1) = halfTurnX (Y z.1) := hx z
    rw [he]
    ext j; fin_cases j <;> simp [halfTurnX,halfTurnZ,P]
  have hk (u v : Fin 3 → ℝ) (c : ℝ) (h : ∀ p, similarityNormal P N u v c p = 0) :
      u = 0 ∧ v = 0 ∧ c = 0 :=
    embedded_torus_similarity_normal_independent L X hX (fun z hz => ⟨analyticAt_pi_iff.mpr
      (fun j => _root_.HarmonicAt.analyticAt (hY.harmonic z hz j)),hY.conformal z hz,hY.immersion z hz⟩) u v c
      (fun z hz => h ⟨z,hz⟩)
  obtain ⟨ha,hb⟩ := two_axis_odd_similarity_normal_only_dilation (X := P) (N := N) (ρX := rx) (ρZ := rz)
    hx (fun z => (harmonic_axis_oriented_normals hL hY z.2).1)
    hv (fun z => (harmonic_axis_oriented_normals hL hY z.2).2) hk
    (fun z => hoddX z.1 z.2) (fun z => hoddZ z.1 z.2)
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const d).exp.mul_const pitch).deriv
  have stable : (fun s : ℝ => Real.exp (s*d)*pitch) =ᶠ[𝓝 0] (fun _ => pitch) := hfix
  have zero : deriv (fun s : ℝ => Real.exp (s*d)*pitch) 0 = 0 :=
    stable.deriv_eq.trans (deriv_const _ _)
  change deriv (fun s : ℝ => Real.exp (s*d)*pitch) 0 = _ at hd
  rw [zero] at hd
  exact ⟨ha,hb,(mul_eq_zero.mp (by simpa using hd.symm : d*pitch = 0)).resolve_right hp⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_axes_and_pitch_remove_similarity_fields
