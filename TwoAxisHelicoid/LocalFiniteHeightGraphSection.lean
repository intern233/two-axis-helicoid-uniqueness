import TwoAxisHelicoid.FiniteNormalGraphSheets
import TwoAxisHelicoid.OrderedCoreSections

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- A set in signed tube coordinates is locally a positive finite union
of distinct scalar graphs. Sheet labels and multiplicities may vary
with the selected base neighborhood. -/
def HasLocalFiniteHeightGraphs {B : Type*} [TopologicalSpace B] (A : Set (B × ℝ)) : Prop :=
  ∀ b : B, ∃ (k : ℕ) (u : Fin (k+1) → B → ℝ),
    (∀ i, ContinuousAt (u i) b) ∧ Function.Injective (fun i => u i b) ∧
    ∀ᶠ v in 𝓝 b, {t : ℝ | (v,t)∈A}=range (fun i => u i v)

/-- The lowest physical height in every fiber is an open sheet over
the entire base, even when the finite local sheet labels vary. -/
theorem lowest_open_section_of_local_height_graphs {B : Type*} [TopologicalSpace B] [T2Space B]
    (A : Set (B × ℝ)) (graphs : HasLocalFiniteHeightGraphs A) :
    ∃ s : B → A, IsOpenEmbedding s ∧ (∀ b, (s b).1.1=b) ∧
      ∀ b (t : ℝ), (b,t)∈A → (s b).1.2≤t := by
  classical
  let p (q : A) := q.1.1
  let h (q : A) := q.1.2
  have germ (b : B) : Nonempty (FiniteSheetGerms p b) := by
    obtain ⟨k,u,cont,distinct,fiber⟩ := graphs b
    have member (i : Fin (k+1)) : ∀ᶠ v in 𝓝 b, (v,u i v)∈A := by
      filter_upwards [fiber] with v eq
      exact (show u i v∈{t : ℝ | (v,t)∈A} from eq.symm ▸ mem_range_self i)
    let fallback : A := ⟨(b,u 0 b),(member 0).self_of_nhds⟩
    let lift (i : Fin (k+1)) (v : B) : A := if ok : (v,u i v)∈A then ⟨(v,u i v),ok⟩ else fallback
    have agrees (i : Fin (k+1)) : (fun v => (lift i v).1) =ᶠ[𝓝 b] fun v => (v,u i v) := by
      filter_upwards [member i] with v ok
      simp only [lift, dite_eq_left ok]
    have atBase (i : Fin (k+1)) : (lift i b).1 = (b, u i b) :=
      (agrees i).self_of_nhds
    refine ⟨⟨k,lift,?_,?_,?_⟩⟩
    · intro i
      apply tendsto_subtype_rng.mpr
      rw [atBase i]
      exact (continuousAt_id.prodMk (cont i)).tendsto.congr' (agrees i).symm
    · intro i j eq
      have base := congrArg (fun q : A => q.1.2) eq
      change (lift i b).1.2=(lift j b).1.2 at base
      rw [atBase i, atBase j] at base
      exact distinct base
    · filter_upwards [fiber,eventually_all.mpr agrees] with v exactFiber chosen
      ext q
      constructor
      · intro hq
        change q.1.1=v at hq
        have height : (v,q.1.2)∈A := hq ▸ q.2
        obtain ⟨i,ui⟩ := (show q.1.2∈range (fun i => u i v) from exactFiber ▸ height)
        refine ⟨i,Subtype.ext ?_⟩
        rw [chosen i]
        exact Prod.ext hq.symm ui
      · rintro ⟨i,rfl⟩
        change (lift i v).1.1=v
        rw [chosen i]
  let G (b : B) := (germ b).some
  have cp : Continuous p := continuous_fst.comp continuous_subtype_val
  obtain ⟨proper,localMap,onto⟩ := proper_projection_of_finite_sheet_germs cp G
  have ch : Continuous h := continuous_snd.comp continuous_subtype_val
  obtain ⟨s,op,base,low⟩ := lowest_fiber_open_section proper localMap onto ch
    (fun a b hp hh => Subtype.ext (Prod.ext hp hh))
  exact ⟨s,op,base,fun b t ht => low b ⟨(b,t),ht⟩ rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lowest_open_section_of_local_height_graphs
