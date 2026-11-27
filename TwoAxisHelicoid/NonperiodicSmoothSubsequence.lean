import TwoAxisHelicoid.FixedAxisAnalyticCompactness
import TwoAxisHelicoid.OriginalCompactCoreFluxGap
import TwoAxisHelicoid.PlacedGraphPointedConclusion

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology InnerProductSpace

/-- Physical point and both unit-normal directions in the regular
coordinates of a normalized punctured torus. -/
def PitchNormalizedBasicImmersion.pointNormals (W : PitchNormalizedBasicImmersion) :
    Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace) :=
  {p | ∃ z∉(rhombicPeriodPair W.t W.ht).lattice,
    coordinateToEuclidean (W.position z)=p.1 ∧ ‖p.2‖=1 ∧
    ∀ v : ℂ, ⟪fderiv ℝ (coordinateToEuclidean ∘ W.position) z v,p.2⟫_ℝ=0}

/-- The physical nonperiodic sequence in the flux argument can be given
a common marked punctured-plane coordinate. All spatial derivatives
converge on every compact set and the complete point-normal sets agree
on the subsequence. All witnesses come from the given sequence. -/
theorem nonperiodic_fixed_axis_smooth_subsequence (x : ℕ → positiveUnitPitchFamily) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      let W := fun n => (x (φ n)).1
      let U := ((rhombicPeriodPair (W 0).t (W 0).ht).lattice : Set ℂ)ᶜ
      (∀ n, (W n).t=(W 0).t ∧ (W n).image=(W 0).image ∧ (W n).pointNormals=(W 0).pointNormals) ∧
        ∀ (k : ℕ) (K : Set ℂ), IsCompact K → K⊆U →
          TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (coordinateToEuclidean ∘ (W n).position))
            (iteratedFDeriv ℝ k (coordinateToEuclidean ∘ (W 0).position)) atTop K := by
  obtain ⟨φ,inc,agree⟩ := fixed_axis_positive_pitch_stationary_subsequence x
  refine ⟨φ,inc,?_⟩
  let W := fun n => (x (φ n)).1
  let L := rhombicPeriodPair (W 0).t (W 0).ht
  let X := fun n => coordinateToEuclidean ∘ (W n).position
  have value (n : ℕ) {z : ℂ} (hz : z∉L.lattice) : X n z=X 0 z :=
    congrArg coordinateToEuclidean ((agree n).2 z hz)
  have germ (n : ℕ) {z : ℂ} (hz : z∉L.lattice) : X n=ᶠ[𝓝 z] X 0 := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with y hy using value n hy
  have sameDom (n : ℕ) : ((rhombicPeriodPair (W n).t (W n).ht).lattice : Set ℂ)=L.lattice := by
    dsimp only [L]
    simp only [show (W n).t=(W 0).t from (agree n).1]
  constructor
  · intro n
    refine ⟨(agree n).1,?_,?_⟩
    · unfold PitchNormalizedBasicImmersion.image
      rw [sameDom n]
      exact image_congr (fun z hz => value n hz)
    · ext p
      change (∃ z∉((rhombicPeriodPair (W n).t (W n).ht).lattice:Set ℂ), X n z=p.1 ∧ ‖p.2‖=1 ∧
        ∀ v : ℂ, ⟪fderiv ℝ (X n) z v,p.2⟫_ℝ=0) ↔
          ∃ z∉(L.lattice:Set ℂ), X 0 z=p.1 ∧ ‖p.2‖=1 ∧ ∀ v : ℂ, ⟪fderiv ℝ (X 0) z v,p.2⟫_ℝ=0
      rw [sameDom n]
      constructor
      · rintro ⟨z,hz,hp,un,hN⟩
        rw [value n hz] at hp
        rw [(germ n hz).fderiv_eq (𝕜:=ℝ)] at hN
        exact ⟨z,hz,hp,un,hN⟩
      · rintro ⟨z,hz,hp,un,hN⟩
        rw [← value n hz] at hp
        rw [← (germ n hz).fderiv_eq (𝕜:=ℝ)] at hN
        exact ⟨z,hz,hp,un,hN⟩
  · intro k K _ sub entourage he
    apply Eventually.of_forall
    intro n z hz
    have d := ((germ n (sub hz)).iteratedFDeriv ℝ k).eq_of_nhds
    change (iteratedFDeriv ℝ k (X 0) z,iteratedFDeriv ℝ k (X n) z)∈entourage
    rw [d]
    exact refl_mem_uniformity he

/-- Application to a sequence of arbitrary spatial placements of the
original C¹ graph-ended surfaces. Each normalization is a positive
Euclidean similarity, and the limit is itself a normalized member of
the original sequence. -/
theorem placed_graph_smooth_subsequence (s : ℕ → PlacedGraphHelicoid) :
    ∃ (w : ℕ → positiveUnitPitchFamily) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, (spatialSimilaritySetoid _).r (s n).1.image (w n).1.image) ∧
      let W := fun n => (w (φ n)).1
      let U := ((rhombicPeriodPair (W 0).t (W 0).ht).lattice : Set ℂ)ᶜ
      (∀ n, (W n).t=(W 0).t ∧ (W n).image=(W 0).image ∧ (W n).pointNormals=(W 0).pointNormals) ∧
        ∀ (k : ℕ) (K : Set ℂ), IsCompact K → K⊆U →
          TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (coordinateToEuclidean ∘ (W n).position))
            (iteratedFDeriv ℝ k (coordinateToEuclidean ∘ (W 0).position)) atTop K := by
  classical
  have pick (n : ℕ) : ∃ w : positiveUnitPitchFamily, (spatialSimilaritySetoid _).r (s n).1.image w.1.image := by
    obtain ⟨W,hw,rel⟩ := graph_surface_has_positive_pitch_model (s n).normalizedGraph
    exact ⟨⟨W,hw⟩,(spatialSimilaritySetoid _).trans (s n).1.image_equivalent_normalized rel⟩
  choose w hw using pick
  obtain ⟨φ,hφ,out⟩ := nonperiodic_fixed_axis_smooth_subsequence w
  exact ⟨w,φ,hφ,hw,out⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonperiodic_fixed_axis_smooth_subsequence
#print axioms TwoAxisHelicoid.placed_graph_smooth_subsequence
