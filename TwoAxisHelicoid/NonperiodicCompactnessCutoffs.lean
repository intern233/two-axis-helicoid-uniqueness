import TwoAxisHelicoid.OriginalSurfaceNonperiodicity
import TwoAxisHelicoid.HorizontalLineCoordinates

namespace TwoAxisHelicoid
open Set Filter Topology Complex
open scoped Topology

/-- The upper and lower local limits of the actual spatial images. Smooth
convergence on compact sets in particular identifies this underlying set. -/
def LocalSpatialImageLimit {E : Type*} [TopologicalSpace E] (S : ℕ → Set E) (L : Set E) : Prop :=
  (∀ x ∈ L, ∀ V ∈ 𝓝 x, ∀ᶠ n in atTop, ∃ y ∈ S n, y ∈ V) ∧
    ∀ x ∉ L, ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, Disjoint (S n) V

theorem LocalSpatialImageLimit.subsequence {E : Type*} [TopologicalSpace E] {S : ℕ → Set E} {L : Set E}
    (h : LocalSpatialImageLimit S L) {φ : ℕ → ℕ} (hφ : StrictMono φ) : LocalSpatialImageLimit (S ∘ φ) L := by
  refine ⟨fun x hx V hV => hφ.tendsto_atTop (h.1 x hx V hV),?_⟩
  intro x hx
  obtain ⟨V,hV,hdis⟩ := h.2 x hx
  exact ⟨V,hV,hφ.tendsto_atTop hdis⟩

theorem LocalSpatialImageLimit.unique {E : Type*} [TopologicalSpace E] {S : ℕ → Set E} {L K : Set E}
    (hL : LocalSpatialImageLimit S L) (hK : LocalSpatialImageLimit S K) : L = K := by
  have sub {A B : Set E} (a : LocalSpatialImageLimit S A) (b : LocalSpatialImageLimit S B) : A ⊆ B := by
    intro x hx
    by_contra hn
    obtain ⟨V,hV,hd⟩ := b.2 x hn
    obtain ⟨n,⟨y,hy,hv⟩,hno⟩ := ((a.1 x hx V hV).and hd).exists
    exact Set.disjoint_left.mp hno hy hv
  exact Subset.antisymm (sub hL hK) (sub hK hL)

/-- The screw motion of the positively normalized standard helicoid through
angle and vertical displacement `2h`, as used in the HWV half-period. -/
noncomputable def unitHelicoidScrew (h : ℝ) : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) :=
  (unitVerticalRotation (exp ((2*h:ℝ)*I)) (by simp [Complex.norm_exp])).toHomeomorph.trans (Homeomorph.addRight ![0,0,2*h])

theorem unitHelicoidScrew_height (h : ℝ) (v : Fin 3 → ℝ) : unitHelicoidScrew h v 2 = v 2+2*h := by
  simp [unitHelicoidScrew,unitVerticalRotation,verticalRotation_apply]

def HasNoScrewBelow (η : ℝ) (S : Set (Fin 3 → ℝ)) : Prop :=
  ∀ h : ℝ, 0 < h → h < η → unitHelicoidScrew h '' S ≠ S

/-- The underlying-image consequence of compactness of each class Nη in
Hoffman--White Theorem 7.1. The limit still belongs to that same cutoff. -/
def CompactScrewCutoffs (family : Set (Set (Fin 3 → ℝ))) : Prop :=
  ∀ η : ℝ, Real.pi/2 < η → ∀ S : ℕ → Set (Fin 3 → ℝ), (∀ n, S n ∈ family ∧ HasNoScrewBelow η (S n)) →
    ∃ (φ : ℕ → ℕ) (L : Set (Fin 3 → ℝ)), StrictMono φ ∧ L ∈ family ∧
      LocalSpatialImageLimit (S ∘ φ) L ∧ HasNoScrewBelow η L

/-- Every spatial subsequential limit of nonperiodic surfaces in the
family has no positive screw period. Apply compactness to a further
subsequence at a cutoff strictly larger than the proposed half-period. -/
theorem nonperiodic_limits_of_compact_screw_cutoffs {family : Set (Set (Fin 3 → ℝ))}
    (hc : CompactScrewCutoffs family) (S : ℕ → Set (Fin 3 → ℝ)) (hS : ∀ n, S n ∈ family)
    (hn : ∀ n h, 0 < h → unitHelicoidScrew h '' S n ≠ S n) {L : Set (Fin 3 → ℝ)}
    (hlim : LocalSpatialImageLimit S L) (h : ℝ) (hh : 0 < h) : unitHelicoidScrew h '' L ≠ L := by
  let η := max (Real.pi/2) h+1
  have hη : Real.pi/2 < η := by dsimp [η]; linarith [le_max_left (Real.pi/2) h]
  have hη' : h < η := by dsimp [η]; linarith [le_max_right (Real.pi/2) h]
  obtain ⟨φ,K,hφ,_,hK,below⟩ := hc η hη S (fun n => ⟨hS n,fun k hk _ => hn n k hk⟩)
  rw [(hlim.subsequence hφ).unique hK]
  exact below h hh hη'

/-- For the actual original embedded once-punctured tori, geometric
nonperiodicity is proved from their topology and Euclidean position. -/
theorem original_surfaces_nonperiodic_limit {family : Set (Set (Fin 3 → ℝ))} (hc : CompactScrewCutoffs family)
    (s : ℕ → OriginalSmoothHelicoid) (hs : ∀ n, range (s n).position ∈ family) :
    ∃ (φ : ℕ → ℕ) (L : Set (Fin 3 → ℝ)), StrictMono φ ∧ L ∈ family ∧
      LocalSpatialImageLimit (fun n => range (s (φ n)).position) L ∧
      ∀ h : ℝ, 0 < h → unitHelicoidScrew h '' L ≠ L := by
  have hn (n : ℕ) (h : ℝ) (hh : 0 < h) := (s n).no_nonzero_screw_step (unitHelicoidScrew h)
    (d := 2*h) (by positivity) (unitHelicoidScrew_height h)
  obtain ⟨φ,L,hφ,hL,hlim,_⟩ := hc (Real.pi/2+1) (by linarith) (fun n => range (s n).position)
    (fun n => ⟨hs n,fun k hk _ => hn n k hk⟩)
  exact ⟨φ,L,hφ,hL,hlim,nonperiodic_limits_of_compact_screw_cutoffs hc _ (fun n => hs (φ n)) (fun n => hn (φ n)) hlim⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_surfaces_nonperiodic_limit
