import TwoAxisHelicoid.NormalCoverSmoothOpenCore
import TwoAxisHelicoid.NormalGraphDerivativeConvergence
import TwoAxisHelicoid.PeriodicCoreLimitExclusion
import TwoAxisHelicoid.LocalDerivativeCoreTransport

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff

/-- A normal-coordinate patch over a relatively compact open core.
The patch can have several connected components. The covering has no
specified degree, and smooth local inverses are given only as germs. -/
structure TorusNormalCorePatch {A : PeriodPair} (C : TorusGeneratingCoreModel A) (L : PeriodPair) where
  patch : Set (PeriodTorus L)
  isOpen_patch : IsOpen patch
  avoids : ∀ q : patch, q.1 ≠ 0
  project : patch → C.carrier
  proper : IsProperMap project
  localHomeomorph : IsLocalHomeomorph project
  onto : Function.Surjective project
  height : patch → ℝ
  continuous_height : Continuous height
  separates : ∀ x y, project x = project y → height x = height y → x = y
  inverseGerms : ∀ q, ∃ f : PeriodTorus A → PeriodTorus L,
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 f (project q).1 ∧ ∀ᶠ b in 𝓝 q, f (project b).1 = b.1

noncomputable def TorusNormalCorePatch.planeHeight {A L : PeriodPair} {C : TorusGeneratingCoreModel A}
    (D : TorusNormalCorePatch C L) (z : ℂ) : ℝ := by
  classical
  exact if hz : periodTorusProjection A z ∈ C.carrier then D.height (D.onto ⟨_,hz⟩).choose else 0

/-- The two separated core patches obtained by following two translated
fundamental slabs of a periodic genus-one limit. -/
def HasTwoPeriodicCorePatches (W : PitchNormalizedBasicImmersion) : Prop :=
  ∃ (A : PeriodPair) (C : TorusGeneratingCoreModel A) (h : ℝ) (v : C.carrier → ℝ)
    (P Q : TorusNormalCorePatch C (rhombicPeriodPair W.t W.ht)), 0 < h ∧ (∀ q, v q ∈ Ioo (-h) h) ∧
    (∀ x : P.patch, |W.torusPosition x.1 2-v (P.project x)| < h) ∧
    ∀ y : Q.patch, |W.torusPosition y.1 2-(v (Q.project y)+4*h)| < h

theorem excluded_periodic_core_patches (W : PitchNormalizedBasicImmersion) : ¬ HasTwoPeriodicCorePatches W := by
  rintro ⟨A,C,h,v,P,Q,hh,hv,hP,hQ⟩
  exact periodic_core_limit_excluded_of_ordered_normal_covers C hh v hv (fun q => WithLp.ofLp (W.torusPosition q))
    Subtype.val Subtype.val P.isOpen_patch.isOpenEmbedding_subtypeVal Q.isOpen_patch.isOpenEmbedding_subtypeVal
    P.proper Q.proper P.localHomeomorph Q.localHomeomorph P.onto Q.onto P.continuous_height Q.continuous_height
    P.separates Q.separates hP hQ

/-- The geometric subsequence-and-local-graph conclusion needed from
the genus-one helicoid compactness theorem. Its two possible limits are
the periodic case and sheets with C¹-small normal height on the core of
a once-punctured torus. Derivative estimates on the selected graph are
used once the normal projections have been proved injective. -/
def HasLocalNormalGraphLimitSubsequence {S : Set PitchNormalizedBasicImmersion} (x : ℕ → S) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ((∃ n, HasTwoPeriodicCorePatches (x (φ n)).1) ∨
    ∃ (A : PeriodPair) (C : TorusGeneratingCoreModel A)
      (D : ∀ n, TorusNormalCorePatch C (rhombicPeriodPair (x (φ n)).1.t (x (φ n)).1.ht))
      (X N : ℂ → EuclideanSpace ℝ (Fin 3)),
      let U := periodTorusProjection A ⁻¹' C.carrier
      (∀ z ∈ U, ContDiffAt ℝ 1 X z) ∧ (∀ z ∈ U, ContDiffAt ℝ 1 N z) ∧
      (∀ n, Function.Injective (D n).project → ∀ z ∈ U, DifferentiableAt ℝ (D n).planeHeight z) ∧
      (∀ n (b : (D n).patch) z, ((D n).project b).1 = periodTorusProjection A z →
        (x (φ n)).1.torusPosition b.1 = X z+(D n).height b • N z) ∧
      ((∀ n, Function.Injective (D n).project) →
        TendstoLocallyUniformlyOn (fun n => (D n).planeHeight) (fun _ => 0) atTop U ∧
        TendstoLocallyUniformlyOn (fun n => fderiv ℝ (D n).planeHeight) (fun _ => 0) atTop U))

def HasLocalNormalGraphLimits (S : Set PitchNormalizedBasicImmersion) : Prop :=
  ∀ x : ℕ → S, HasLocalNormalGraphLimitSubsequence x

theorem local_normal_graph_limits_supply_core_compactness {S : Set PitchNormalizedBasicImmersion}
    (h : HasLocalNormalGraphLimits S) : HasLocalC1CoreCompactness S := by
  classical
  intro x
  obtain ⟨φ,hφ,hp | hn⟩ := h x
  · obtain ⟨n,hn⟩ := hp
    exact (excluded_periodic_core_patches _ hn).elim
  obtain ⟨A,C,D,X,N,hX,hN,hd,hgraph,hsmall⟩ := hn
  choose F hF using fun n => normal_cover_gives_smooth_open_core C Subtype.val
    (D n).isOpen_patch.isOpenEmbedding_subtypeVal (D n).avoids (D n).proper (D n).localHomeomorph
    (D n).onto (D n).continuous_height (D n).separates (D n).inverseGerms
  have hinj (n : ℕ) : Function.Injective (D n).project := by
    intro x y eq
    apply Subtype.ext
    rw [← hF n x,← hF n y,eq]
  obtain ⟨h₀,h₁⟩ := hsmall hinj
  let Z := fun n => (x (φ n)).1.torusPosition ∘ (F n).map ∘ periodTorusProjection A
  have he (n : ℕ) (z : ℂ) (hz : periodTorusProjection A z ∈ C.carrier) :
      Z n z = X z+(D n).planeHeight z • N z := by
    let q : C.carrier := ⟨_,hz⟩
    let b := ((D n).onto q).choose
    have hb : ((D n).project b).1 = periodTorusProjection A z := congrArg Subtype.val ((D n).onto q).choose_spec
    have hf : (F n).map (periodTorusProjection A z) = b.1 := hb ▸ hF n b
    change (x (φ n)).1.torusPosition ((F n).map (periodTorusProjection A z)) = _
    rw [hf]
    simpa only [TorusNormalCorePatch.planeHeight,dite_eq_left hz] using hgraph n b z hb
  have hu : IsOpen (periodTorusProjection A ⁻¹' C.carrier) := C.isOpen_carrier.preimage QuotientAddGroup.continuous_mk
  have ⟨hdZ,hconv⟩ := normal_graph_spatial_derivative_convergence hu X N Z _ hX hN
    (fun n => hd n (hinj n)) he h₀ h₁
  exact ⟨φ,hφ,A,C,F,X,hdZ,hX,hconv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.excluded_periodic_core_patches
#print axioms TwoAxisHelicoid.local_normal_graph_limits_supply_core_compactness
