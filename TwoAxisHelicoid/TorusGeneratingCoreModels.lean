import TwoAxisHelicoid.OpenPuncturedCoreConnectivity
import TwoAxisHelicoid.TorusCompactCoreDetection
import TwoAxisHelicoid.PeriodTorusComplexManifold

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A relatively compact open subsurface of the punctured torus with
specified generator loops and a collapse map available after every open
embedding into another marked torus. -/
structure TorusGeneratingCoreModel (A : PeriodPair) where
  carrier : Set (PeriodTorus A)
  isOpen_carrier : IsOpen carrier
  pathConnected : PathConnectedSpace carrier
  closure_avoids : (0 : PeriodTorus A) ∉ closure carrier
  base : carrier
  loop : Fin 2 → Path base base
  projects : ∀ i (s : unitInterval), (loop i s).1 = (puncturedTorusGeneratorLoop A i s).1
  detect : ∀ (L : PeriodPair) (f : carrier → PeriodTorus L), IsOpenEmbedding f →
    ∃ F : C(PeriodTorus L,PeriodTorus A), (∀ i s, F (f (loop i s)) = (loop i s).1) ∧
      ∀ y ∉ range f, F y = 0

/-- The prescribed genus-one core exists for each actual marked complex
torus. Its two loops are the same concrete basis curves already identified
in the fundamental group. -/
theorem exists_torus_generating_core_model (A : PeriodPair) : Nonempty (TorusGeneratingCoreModel A) := by
  classical
  let := periodTorus_compactSpace A
  let : T1Space (PeriodTorus A) := QuotientAddGroup.t1Space_iff.mpr A.isClosed_lattice
  let p := (0 : PeriodTorus A)
  let e := (periodTorusInverseChart A p).symm
  have hp : p ∈ e.source := periodTorusInverseChart_target A p
  let K : Set (PeriodTorus A) := Subtype.val '' puncturedGeneratorCore A
  have hK : IsCompact K := (puncturedGeneratorCore_isCompact A).image continuous_subtype_val
  have hsep : p ∉ K := by rintro ⟨q,_,hq⟩; exact q.2 hq
  obtain ⟨r,hr,hB,hoff⟩ := chart_disk_away_from_compact e hp hK hsep
  let U := openChartCore e p r
  have hhalf : closedBall (e p) (r/2) ⊆ closedBall (e p) (2*r) := closedBall_subset_closedBall (by linarith)
  have hU : IsOpen U := ((isCompact_closedBall (e p) (r/2)).image_of_continuousOn (e.continuousOn_symm.mono (hhalf.trans hB))).isClosed.isOpen_compl
  have hn (q : PuncturedPeriodTorus A) (hq : q ∈ puncturedGeneratorCore A) : q.1 ∈ U :=
    fun h => hoff q.1 ⟨q,hq,rfl⟩ ((image_mono hhalf) h)
  have hb : (puncturedTorusCenter A).1 ∈ U := by
    apply hn
    simpa using puncturedTorusGeneratorLoop_mem_core A 0 0
  let b : U := ⟨(puncturedTorusCenter A).1,hb⟩
  let γ (i : Fin 2) : Path b b := {
    toFun := fun s => ⟨(puncturedTorusGeneratorLoop A i s).1,hn _ (puncturedTorusGeneratorLoop_mem_core A i s)⟩
    continuous_toFun := (continuous_subtype_val.comp (puncturedTorusGeneratorLoop A i).continuous).subtype_mk _
    source' := Subtype.ext (congrArg (fun q : PuncturedPeriodTorus A => q.1) (puncturedTorusGeneratorLoop A i).source)
    target' := Subtype.ext (congrArg (fun q : PuncturedPeriodTorus A => q.1) (puncturedTorusGeneratorLoop A i).target) }
  have hcl : p ∉ closure U := by
    let V := e.symm '' ball (e p) (r/2)
    have hV : IsOpen V := e.isOpen_image_symm_of_subset_target isOpen_ball (ball_subset_closedBall.trans (hhalf.trans hB))
    have hsub : U ⊆ Vᶜ := fun _ hx h => hx ((image_mono ball_subset_closedBall) h)
    exact fun h => closure_minimal hsub hV.isClosed_compl h ⟨e p,mem_ball_self (half_pos hr),e.left_inv hp⟩
  have hpc : PathConnectedSpace U := open_chart_core_path_connected e hp hr hB ⟨b⟩ (punctured_torus_is_path_connected A)
  refine ⟨⟨U,hU,hpc,hcl,b,γ,fun _ _ => rfl,?_⟩⟩
  intro L f hf
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  obtain ⟨F,hF,ho⟩ := chart_core_admits_detecting_map e hp hr hB f hf
  refine ⟨F,fun i s => hF (γ i s) ?_,ho⟩
  exact fun h => hoff _ ⟨_,puncturedTorusGeneratorLoop_mem_core A i s,rfl⟩ ((image_mono ball_subset_closedBall) h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_torus_generating_core_model
