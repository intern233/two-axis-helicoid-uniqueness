import TwoAxisHelicoid.CompactAvoidingLogarithm
import TwoAxisHelicoid.ExtremalDiskCoordinates

namespace TwoAxisHelicoid
open Complex Set Topology Metric

/-- A logarithm on the union of the ranges of two paths makes their
lift endpoints agree. This gives one continuous logarithm on the whole
one-ended plane domain for each omitted point. -/
theorem one_ended_plane_omitted_log {V : Set ℂ} (op : IsOpen V) (connected : IsConnected V)
    (tails : HasConnectedCompactTails V) {a : ℂ} (outsidePoint : a∉V) :
    ∃ l : ℂ → ℂ, ContinuousOn l V ∧ ∀ z∈V, exp (l z)=z-a := by
  classical
  let _ : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp (op.isConnected_iff_isPathConnected.mp connected)
  let _ : LocallyPathConnectedSpace V := op.locallyPathConnectedSpace
  let E := {z : ℂ // z≠0}
  let π := fun u : ℂ => (⟨exp u,exp_ne_zero u⟩:E)
  have cov : IsCoveringMap π := Complex.isCoveringMap_exp
  let f : C(V,E) := ⟨fun z => ⟨z.1-a,sub_ne_zero.mpr fun eq => outsidePoint (eq ▸ z.2)⟩,
    (continuous_subtype_val.sub continuous_const).subtype_mk _⟩
  obtain ⟨p,mem⟩ := connected.nonempty
  let p₀ : V := ⟨p,mem⟩
  let e₀ := log (p-a)
  have base : π e₀=f p₀ := Subtype.ext (exp_log (f p₀).2)
  have unique (γ δ : C(unitInterval,V)) (A B : C(unitInterval,ℂ))
      (g0 : γ 0=p₀) (d0 : δ 0=p₀) (a0 : A 0=e₀) (b0 : B 0=e₀)
      (pa : π ∘ A=f.comp γ) (pb : π ∘ B=f.comp δ) (ends : γ 1=δ 1) : A 1=B 1 := by
    let c := fun t : unitInterval => (γ t).1
    let d := fun t : unitInterval => (δ t).1
    let K := range c∪range d
    have ck : IsCompact K := (isCompact_range (continuous_subtype_val.comp γ.continuous)).union
      (isCompact_range (continuous_subtype_val.comp δ.continuous))
    have inside : K⊆V := union_subset (range_subset_iff.mpr fun t => (γ t).2) (range_subset_iff.mpr fun t => (δ t).2)
    obtain ⟨L,logL⟩ := compact_logarithm_at_omitted_point op tails ck inside ⟨c 0,Or.inl (mem_range_self _)⟩ outsidePoint
    let j : C(unitInterval,K) := ⟨fun t => ⟨c t,Or.inl (mem_range_self _)⟩,(continuous_subtype_val.comp γ.continuous).subtype_mk _⟩
    let k : C(unitInterval,K) := ⟨fun t => ⟨d t,Or.inr (mem_range_self _)⟩,(continuous_subtype_val.comp δ.continuous).subtype_mk _⟩
    have start : k 0=j 0 := Subtype.ext (congrArg (fun w : V => w.1) (d0.trans g0.symm))
    let D := fun z : K => L z+(e₀-L (j 0))
    have cd : Continuous D := L.continuous.add continuous_const
    have dz : D (j 0)=e₀ := by dsimp [D]; abel
    have pr (z : K) : π (D z)=⟨z.1-a,sub_ne_zero.mpr fun eq => outsidePoint (eq ▸ inside z.2)⟩ := by
      apply Subtype.ext
      change exp (L z+(e₀-L (j 0)))=z.1-a
      rw [exp_add,exp_sub,logL,logL]
      have origin : (j 0).1=p := congrArg Subtype.val g0
      rw [origin,show exp e₀=p-a from congrArg Subtype.val base,div_self (show p-a≠0 from (f p₀).2),mul_one]
    have left : (A : unitInterval → ℂ)=D ∘ j := cov.eq_of_comp_eq A.continuous (cd.comp j.continuous)
      (funext fun t => (congrFun pa t).trans (pr (j t)).symm) 0 (a0.trans dz.symm)
    have right : (B : unitInterval → ℂ)=D ∘ k := cov.eq_of_comp_eq B.continuous (cd.comp k.continuous)
      (funext fun t => (congrFun pb t).trans (pr (k t)).symm) 0 (by rw [Function.comp_apply,start,dz,b0])
    exact (congrFun left 1).trans ((congrArg D (Subtype.ext (congrArg (fun w : V => w.1) ends))).trans (congrFun right 1).symm)
  obtain ⟨L,⟨_,eq⟩,_⟩ := cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f p₀ e₀ base
    (fun γ g0 => by
      obtain ⟨G,e,b⟩ := cov.exists_path_lifts (f.comp γ) e₀ (by change f (γ 0)=π e₀; rw [g0,base])
      exact ⟨G,b,e⟩) unique
  let l := fun z : ℂ => if m : z∈V then L ⟨z,m⟩ else 0
  refine ⟨l,continuousOn_iff_continuous_domRestrict.mpr ?_,fun z hz => ?_⟩
  · have ident : V.domRestrict l=L := by funext z; simp [l,z.2]
    rw [ident]
    exact L.continuous
  · simpa [l,hz,π,f] using congrArg Subtype.val (congrFun eq (⟨z,hz⟩:V))

/-- The omitted coordinate therefore has a single-valued analytic
square root on the whole domain. -/
theorem one_ended_plane_omitted_square_root {V : Set ℂ} (op : IsOpen V) (connected : IsConnected V)
    (tails : HasConnectedCompactTails V) {a : ℂ} (outsidePoint : a∉V) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q V ∧ ∀ z∈V, q z^2=z-a := by
  obtain ⟨l,cl,eq⟩ := one_ended_plane_omitted_log op connected tails outsidePoint
  let q := fun z => exp (l z/2)
  have cq : ContinuousOn q V := (cl.div_const 2).cexp
  have sq (z : ℂ) (hz : z∈V) : q z^2=z-a := by
    change exp (l z/2)^2=z-a
    rw [pow_two,← exp_add,show l z/2+l z/2=l z by ring,eq z hz]
  exact ⟨q,analytic_continuous_square_root (h:=fun z => z-a) op cq (fun _ _ => analyticAt_id.sub analyticAt_const) sq
    (fun z hz => sub_ne_zero.mpr fun zero => outsidePoint ((show z=a from zero) ▸ hz)),sq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_plane_omitted_log
#print axioms TwoAxisHelicoid.one_ended_plane_omitted_square_root
