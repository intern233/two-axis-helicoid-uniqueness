import TwoAxisHelicoid.CompactFamilyPhaseObstruction
import TwoAxisHelicoid.BasedLoopPhaseObstruction
import TwoAxisHelicoid.RegularHeightPathDeformation
import Mathlib.Topology.CompactOpen

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology unitInterval

/-- A family of closed paths descends to a common compact connected
quotient of the interval. A closed-angle obstruction on the base path
therefore also occurs on a whole component at each nearby height. -/
theorem nearby_closed_path_height_nonlifting {S M : Type*}
    [TopologicalSpace S] [LocallyCompactSpace S] [TopologicalSpace M]
    (F : C(S×I,M)) (H : C(M,Circle×Circle)) {h : M → ℝ} {v : S → ℝ}
    (height : ∀ s t, h (F (s,t))=v s) (ends : ∀ s, F (s,0)=F (s,1)) (s₀ : S)
    (obstruct : ¬∃ u w : C(I,ℝ), u 0=u 1 ∧ w 0=w 1 ∧ ∀ t,
      normalizedPhase (u t)=(H (F (s₀,t))).1 ∧ normalizedPhase (w t)=(H (F (s₀,t))).2) :
    ∀ᶠ s in 𝓝 s₀, ∃ x : h ⁻¹' {v s}, ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
  let R := Setoid.ker (fun t : I => fun s : S => F (s,t))
  let Q := Quotient R
  let π : C(I,Q) := ⟨Quotient.mk R,continuous_quotient_mk'⟩
  have endpoints : π 0=π 1 := Quotient.sound (show (fun s : S => F (s,0))=(fun s => F (s,1)) from funext ends)
  let G := fun q : S×Q => Quotient.lift (fun t : I => F (q.1,t)) (fun _ _ h => congrFun h q.1) q.2
  have quotient : IsQuotientMap π := isQuotientMap_quotient_mk'
  have cG : Continuous G := quotient.continuous_lift_prod_right (g:=G) F.continuous
  have level (s : S) (q : Q) : h (G (s,q))=v s := by
    obtain ⟨t,rfl⟩ := quotient.surjective q
    exact height s t
  apply nearby_height_component_nonlifting ⟨G,cG⟩ H level s₀ (π 0)
  rintro ⟨u,w,rep⟩
  exact obstruct ⟨u.comp π,w.comp π,congrArg u endpoints,congrArg w endpoints,fun t => rep (π t)⟩

/-- Entire regular loops with a marked obstruction can be shifted to all
sufficiently close heights. Their physical endpoints use the same
local section, hence the deformed paths are still closed. -/
theorem regular_loop_height_obstruction_persists {M : Type*} [TopologicalSpace M]
    (H : C(M,Circle×Circle)) (h : M → ℝ) (v : ℝ) {x : M} (γ : Path x x)
    (level : ∀ t, h (γ t)=v)
    (charts : ∀ t, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), γ t∈e.source ∧
      ∀ w∈e.target, h (e.symm w)=w.2)
    (obstruct : ¬∃ u w : C(I,ℝ), u 0=u 1 ∧ w 0=w 1 ∧ ∀ t,
      normalizedPhase (u t)=(H (γ t)).1 ∧ normalizedPhase (w t)=(H (γ t)).2) :
    ∀ᶠ s in 𝓝 v, ∃ q : h ⁻¹' {s}, ¬∃ a b : C(connectedComponent q,ℝ), ∀ z : connectedComponent q,
      normalizedPhase (a z)=(H z.1.1).1 ∧ normalizedPhase (b z)=(H z.1.1).2 := by
  let values : C(ℝ,ℝ) := ⟨fun s => v+s,continuous_const.add continuous_id⟩
  have lv (t : I) : h (γ t)=values 0 := by simpa [values] using level t
  obtain ⟨e,src,ht⟩ := charts 0
  obtain ⟨P,z,near⟩ := product_height_chart_section e src ht values (lv 0).symm
  have z1 : P 0=γ 1 := z.trans (γ.source.trans γ.target.symm)
  obtain ⟨d,dp,F,cF,F0,each⟩ := regular_height_path_deformation γ.toContinuousMap values lv charts P P z z1 near near
  have ord : -d≤d := by linarith
  let k := fun s : ℝ => (projIcc (-d) d ord (s-v) : ℝ)
  have ck : Continuous k := continuous_subtype_val.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))
  have inside (s : ℝ) : k s∈Icc (-d) d := (projIcc (-d) d ord (s-v)).2
  have fix (s : ℝ) (hs : s-v∈Icc (-d) d) : k s=s-v := congrArg Subtype.val (projIcc_of_mem ord hs)
  have z0 : k v=0 := by
    rw [fix,sub_self]
    simpa only [sub_self] using (show (0:ℝ)∈Icc (-d) d from ⟨neg_nonpos.mpr dp.le,dp.le⟩)
  let K := fun q : ℝ×I => (k q.1,q.2)
  let G : C(ℝ×I,M) := ⟨F ∘ K,cF.comp_continuous ((ck.comp continuous_fst).prodMk continuous_snd)
    (fun q => ⟨inside q.1,mem_univ _⟩)⟩
  have rep (t : I) : G (v,t)=γ t := by change F (k v,t)=γ t; rw [z0]; exact F0 t
  have nearLevel := nearby_closed_path_height_nonlifting G H (h:=h) (v:=fun s => values (k s))
    (fun s => (each (k s) (inside s)).1)
    (fun s => (each (k s) (inside s)).2.1.trans (each (k s) (inside s)).2.2.symm) v
    (by simpa only [rep] using obstruct)
  have close : ∀ᶠ s in 𝓝 v, s-v∈Icc (-d) d :=
    ((continuous_id.sub continuous_const).continuousAt (x:=v)).eventually
      (show Icc (-d) d∈𝓝 (v-v) by rw [sub_self]; exact Icc_mem_nhds (neg_lt_zero.mpr dp) dp)
  filter_upwards [nearLevel,close] with s found small
  have eq : values (k s)=s := by change v+k s=s; rw [fix _ small]; abel
  rwa [eq] at found

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nearby_closed_path_height_nonlifting
#print axioms TwoAxisHelicoid.regular_loop_height_obstruction_persists
