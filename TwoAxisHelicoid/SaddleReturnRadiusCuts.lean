import TwoAxisHelicoid.MarkedSaddleReturn
import TwoAxisHelicoid.SaddleSurgerySquare

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology unitInterval

/-- A nonzero scalar on a continuous final ray that tends to zero
admits all sufficiently small signed radius cuts while preserving
every eventual constraint on the cut point. -/
theorem eventual_signed_radius_cuts {u : ℝ → ℝ} {P : ℝ → Prop}
    (limit : Tendsto u atTop (𝓝 0)) (cond : ∀ᶠ t in atTop, P t ∧ u t≠0 ∧ ContinuousAt u t) :
    ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo 0 R, ∃ t b : ℝ, P t ∧ |b|=1 ∧ u t=b*r := by
  obtain ⟨T,after⟩ := eventually_atTop.mp cond
  refine ⟨|u T|,abs_pos.mpr (after T le_rfl).2.1,?_⟩
  intro r hr
  obtain ⟨t,b,ht,bb,eq⟩ := radial_cuts_on_real_tail
    (T:=T) (fun t ht => (after t ht).2.2.continuousWithinAt) limit r hr
  exact ⟨t,b,(after t ht).1,bb,eq⟩

/-- Orient the plane traversal towards the horizontal arm of the same
physical chart. Reversing the real parameter exchanges its endpoint
lifts and retains regularity at all finite times. -/
theorem oriented_saddle_return {L : PeriodPair} {h : PeriodTorus L → ℝ}
    (ret : HasSeparatedSaddleReturn L h) :
    ∃ (p : PeriodTorus L) (e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ)) (γ : ℝ → ℂ) (a b : ℂ),
      p∈e.source ∧ e p=0 ∧ (∀ᶠ q in 𝓝 p, h q=h p+(e q).1*(e q).2) ∧ Continuous γ ∧
      periodTorusProjection L a=p ∧ periodTorusProjection L b=p ∧ a≠b ∧
      Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b) ∧
      (∀ t, let y := periodTorusProjection L (γ t)
        h y=h p ∧ y≠p ∧ ∃ d : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), y∈d.source ∧
          ∀ w∈d.target, h (d.symm w)=w.2) ∧
      (∀ᶠ t in atBot, (e (periodTorusProjection L (γ t))).1=0) ∧
       ∀ᶠ t in atTop, (e (periodTorusProjection L (γ t))).2=0 := by
  obtain ⟨p,e,γ,a,b,src,zero,model,_,cγ,ap,bp,apart,al,bl,reg,horiz|vert⟩ := ret
  · exact ⟨p,e,γ,a,b,src,zero,model,cγ,ap,bp,apart,al,bl,reg,horiz.2,horiz.1⟩
  · exact ⟨p,e,fun t => γ (-t),b,a,src,zero,model,cγ.comp continuous_neg,bp,ap,apart.symm,
      bl.comp tendsto_neg_atBot_atTop,al.comp tendsto_neg_atTop_atBot,fun t => reg (-t),
      tendsto_neg_atBot_atTop.eventually vert.1,tendsto_neg_atTop_atBot.eventually vert.2⟩

/-- Cut an actual returning saddle orbit at the same small coordinate
radius on its two different arms. Its true plane lifts at the cuts
differ from a common local section by distinct lattice periods. -/
theorem saddle_return_equal_radius_cuts {L : PeriodPair} (γ : ℝ → ℂ) {a b : ℂ} {p : PeriodTorus L}
    (e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ)) (src : p∈e.source) (center : e p=0)
    (cγ : Continuous γ) (ap : periodTorusProjection L a=p) (bp : periodTorusProjection L b=p)
    (al : Tendsto γ atBot (𝓝 a)) (bl : Tendsto γ atTop (𝓝 b)) (away : ∀ t, periodTorusProjection L (γ t)≠p)
    (vert : ∀ᶠ t in atBot, (e (periodTorusProjection L (γ t))).1=0)
    (horiz : ∀ᶠ t in atTop, (e (periodTorusProjection L (γ t))).2=0)
    (d : OpenPartialHomeomorph ℂ (PeriodTorus L)) (ds : a∈d.source) (repr : periodTorusProjection L=d) :
    ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo 0 R, ∃ t₁ t₂ u v : ℝ, |u|=1 ∧ |v|=1 ∧
      (periodTorusProjection L (γ t₁)∈e.source ∧ e (periodTorusProjection L (γ t₁))=(0,v*r) ∧
        d.symm (periodTorusProjection L (γ t₁))=γ t₁) ∧
      (periodTorusProjection L (γ t₂)∈e.source ∧ e (periodTorusProjection L (γ t₂))=(u*r,0) ∧
        d.symm (periodTorusProjection L (γ t₂))=γ t₂-(b-a)) := by
  let π := periodTorusProjection L
  let left := fun t : ℝ => π (γ (-t))
  let right := fun t : ℝ => π (γ t)
  have cπ : Continuous π := QuotientAddGroup.continuous_mk
  have cl : Continuous left := cπ.comp (cγ.comp continuous_neg)
  have cr : Continuous right := cπ.comp cγ
  have ll : Tendsto left atTop (𝓝 p) := ap ▸ cπ.continuousAt.tendsto.comp (al.comp tendsto_neg_atTop_atBot)
  have rl : Tendsto right atTop (𝓝 p) := bp ▸ cπ.continuousAt.tendsto.comp bl
  have ec : ContinuousAt e p := e.continuousAt src
  have ltend : Tendsto (fun t => (e (left t)).2) atTop (𝓝 0) := by
    have limit := ec.snd.tendsto.comp ll
    change Tendsto (fun t => (e (left t)).2) atTop (𝓝 (e p).2) at limit
    rw [center] at limit
    exact limit
  have rtend : Tendsto (fun t => (e (right t)).1) atTop (𝓝 0) := by
    have limit := ec.fst.tendsto.comp rl
    change Tendsto (fun t => (e (right t)).1) atTop (𝓝 (e p).1) at limit
    rw [center] at limit
    exact limit
  let k := b-a
  have kper : k∈L.lattice := (periodTorusProjection_eq_iff L a b).mp (ap.trans bp.symm)
  have shift (z : ℂ) : π (z-k)=π z := by
    apply (periodTorusProjection_eq_iff L _ _).mpr
    simpa only [sub_sub_cancel] using kper
  have bl' : Tendsto (fun t => γ t-k) atTop (𝓝 a) := by
    have val : b-k=a := sub_sub_cancel b a
    exact val ▸ bl.sub (tendsto_const_nhds (x:=k))
  have ls := (al.comp tendsto_neg_atTop_atBot).eventually (d.open_source.mem_nhds ds)
  have rs := bl'.eventually (d.open_source.mem_nhds ds)
  have clean {q : PeriodTorus L} (ins : q∈e.source) (miss : q≠p) : e q≠0 := by
    intro eq
    exact miss (e.injOn ins src (eq.trans center.symm))
  let P₁ := fun t : ℝ => left t∈e.source ∧ (e (left t)).1=0 ∧ d.symm (left t)=γ (-t)
  let P₂ := fun t : ℝ => right t∈e.source ∧ (e (right t)).2=0 ∧ d.symm (right t)=γ t-k
  have leftCond : ∀ᶠ t in atTop, P₁ t ∧ (e (left t)).2≠0 ∧ ContinuousAt (fun t => (e (left t)).2) t := by
    filter_upwards [ll.eventually (e.open_source.mem_nhds src),tendsto_neg_atTop_atBot.eventually vert,ls] with t ins axis sheet
    have sectionEq : d.symm (left t)=γ (-t) := by
      change d.symm (periodTorusProjection L (γ (-t)))=_
      rw [repr]
      exact d.left_inv sheet
    exact ⟨⟨ins,axis,sectionEq⟩,fun eq => clean ins (away (-t)) (Prod.ext axis eq),
      ((e.continuousAt ins).comp cl.continuousAt).snd⟩
  have rightCond : ∀ᶠ t in atTop, P₂ t ∧ (e (right t)).1≠0 ∧ ContinuousAt (fun t => (e (right t)).1) t := by
    filter_upwards [rl.eventually (e.open_source.mem_nhds src),horiz,rs] with t ins axis sheet
    have sectionEq : d.symm (right t)=γ t-k := by
      change d.symm (π (γ t))=_
      rw [← shift (γ t)]
      change d.symm (periodTorusProjection L (γ t-k))=_
      rw [repr]
      exact d.left_inv sheet
    exact ⟨⟨ins,axis,sectionEq⟩,fun eq => clean ins (away t) (Prod.ext eq axis),
      ((e.continuousAt ins).comp cr.continuousAt).fst⟩
  obtain ⟨A,Ap,ca⟩ := eventual_signed_radius_cuts ltend leftCond
  obtain ⟨B,Bp,cb⟩ := eventual_signed_radius_cuts rtend rightCond
  refine ⟨min A B,lt_min Ap Bp,?_⟩
  intro r hr
  obtain ⟨t,v,⟨se,left0,leq⟩,vv,tipV⟩ := ca r ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩
  obtain ⟨s,u,⟨sf,right0,req⟩,uu,tipU⟩ := cb r ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩
  exact ⟨-t,s,u,v,uu,vv,⟨se,Prod.ext left0 tipV,leq⟩,sf,Prod.ext tipU right0,req⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_return_equal_radius_cuts
