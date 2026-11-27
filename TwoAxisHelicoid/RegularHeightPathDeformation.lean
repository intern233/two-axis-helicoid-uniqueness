import TwoAxisHelicoid.HeightChartSegmentDeformation

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped unitInterval Topology

/-- A regular two-dimensional height chart supplies a continuous
transverse section through each of its points. -/
theorem product_height_chart_section {M : Type*} [TopologicalSpace M] {h : M → ℝ}
    {x : M} (e : OpenPartialHomeomorph M (ℝ×ℝ)) (src : x∈e.source)
    (height : ∀ w∈e.target, h (e.symm w)=w.2)
    (v : C(ℝ,ℝ)) (base : v 0=h x) :
    ∃ P : C(ℝ,M), P 0=x ∧ ∀ᶠ s in 𝓝 (0:ℝ), h (P s)=v s := by
  let A := fun s : ℝ => ((e x).1,v s)
  have cA : Continuous A := continuous_const.prodMk v.continuous
  have value := height (e x) (e.map_source src)
  rw [e.left_inv src] at value
  have A0 : A 0=e x := Prod.ext rfl (base.trans value)
  have eventuallyInside : ∀ᶠ s in 𝓝 (0:ℝ), A s∈e.target := cA.continuousAt.eventually
    (e.open_target.mem_nhds (by rw [A0];exact e.map_source src))
  obtain ⟨d,dp,sub⟩ := height_shift_interval_of_eventually eventuallyInside
  have ord : -d≤d := by linarith
  let k := fun s : ℝ => (projIcc (-d) d ord s : ℝ)
  have ck : Continuous k := continuous_subtype_val.comp continuous_projIcc
  have mem (s : ℝ) : A (k s)∈e.target := sub _ (projIcc (-d) d ord s).2
  have kfix (s : ℝ) (hs : s∈Icc (-d) d) : k s=s := congrArg Subtype.val (projIcc_of_mem ord hs)
  let P : C(ℝ,M) := ⟨fun s => e.symm (A (k s)),e.continuousOn_symm.comp_continuous (cA.comp ck) mem⟩
  refine ⟨P,?_,?_⟩
  · change e.symm (A (k 0))=x
    rw [kfix 0 ⟨neg_nonpos.mpr dp.le,dp.le⟩,A0,e.left_inv src]
  · filter_upwards [Icc_mem_nhds (neg_lt_zero.mpr dp) dp] with s hs
    change h (e.symm (A (k s)))=v s
    rw [kfix s hs]
    exact height (A s) (sub s hs)

/-- An entire regular level path on a surface deforms to the nearby
heights with any prescribed continuous endpoint sections on those
heights. Only local charts along the given path are required. -/
theorem regular_height_path_deformation {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} (γ : C(I,M)) (v : C(ℝ,ℝ)) (level : ∀ t, h (γ t)=v 0)
    (charts : ∀ t, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), γ t∈e.source ∧
      ∀ w∈e.target, h (e.symm w)=w.2)
    (a b : C(ℝ,M)) (a0 : a 0=γ 0) (b0 : b 0=γ 1)
    (ah : ∀ᶠ s in 𝓝 (0:ℝ), h (a s)=v s) (bh : ∀ᶠ s in 𝓝 (0:ℝ), h (b s)=v s) :
    ∃ d : ℝ, 0<d ∧ ∃ F : ℝ×I → M, ContinuousOn F (Icc (-d) d ×ˢ univ) ∧
      (∀ t, F (0,t)=γ t) ∧ ∀ s∈Icc (-d) d,
        (∀ t, h (F (s,t))=v s) ∧ F (s,0)=a s ∧ F (s,1)=b s := by
  classical
  choose e ins height using charts
  choose sectionAt sectionZero sectionHeight using fun t => product_height_chart_section (e t) (ins t) (height t) v (level t).symm
  let P := fun t : I => if t=0 then a else if t=1 then b else sectionAt t
  have p0 (t : I) : P t 0=γ t := by
    by_cases l : t=0
    · subst t; simpa only [P,ite_eq_left rfl] using a0
    by_cases r : t=1
    · subst t; simpa [P] using b0
    · simpa only [P,ite_eq_right l,ite_eq_right r] using sectionZero t
  have pv (t : I) : ∀ᶠ s in 𝓝 (0:ℝ), h (P t s)=v s := by
    by_cases l : t=0
    · simpa only [P,ite_eq_left l] using ah
    by_cases r : t=1
    · simpa only [P,ite_eq_right l,ite_eq_left r] using bh
    · simpa only [P,ite_eq_right l,ite_eq_right r] using sectionHeight t
  let U := fun t : I => γ ⁻¹' (e t).source
  have op (t : I) : IsOpen (U t) := (e t).open_source.preimage γ.continuous
  have cover : univ⊆⋃ t, U t := fun t _ => mem_iUnion.mpr ⟨t,ins t⟩
  obtain ⟨cut,first,ordered,⟨N,last⟩,sub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval op cover
  have all : HeightPathDeformationOn h v γ (fun t s => P t s) 0 1 := by
    apply height_path_deformation_of_subdivision cut first (last N le_rfl) ordered
    intro n _
    obtain ⟨i,inside⟩ := sub n
    exact regular_height_chart_segment_deformation (e i) (height i) γ v P p0 pv
      (ordered (Nat.le_succ _)) (fun _ ht => inside ht) (fun t _ => level t)
  obtain ⟨d,dp,F,cont,base,each⟩ := all
  have allI (t : I) : t∈Icc (0:I) 1 := ⟨t.2.1,t.2.2⟩
  refine ⟨d,dp,F,cont.mono (fun q hq => ⟨hq.1,allI q.2⟩),fun t => base t (allI t),?_⟩
  intro s hs
  obtain ⟨lv,left,right⟩ := each s hs
  exact ⟨fun t => lv t (allI t),by simpa only [P,ite_eq_left rfl] using left,
    by simpa [P] using right⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.product_height_chart_section
#print axioms TwoAxisHelicoid.regular_height_path_deformation
