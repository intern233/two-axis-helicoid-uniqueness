import TwoAxisHelicoid.RectangleIntermediateValue
import Mathlib.Topology.Separation.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- Filling two missing boundary points by their separate limits preserves
continuity on the enlarged domain. -/
theorem continuous_fill_two_points {E T : Type*} [TopologicalSpace E] [T1Space E] [TopologicalSpace T]
    {S : Set E} {p q : E} (ne : p≠q) (hp : p∉S) (hq : q∉S) {f : E → T}
    (cf : ContinuousOn f S) {a b : T} (pa : Tendsto f (𝓝[S] p) (𝓝 a)) (qb : Tendsto f (𝓝[S] q) (𝓝 b)) :
    ∃ g : E → T, ContinuousOn g (insert q (insert p S)) ∧ EqOn g f S ∧ g p=a ∧ g q=b := by
  classical
  have fill {V : Set E} {x : E} (hx : x∉V) {h : E → T} (ch : ContinuousOn h V)
      {y : T} (hy : Tendsto h (𝓝[V] x) (𝓝 y)) :
      ContinuousOn (Function.update h x y) (insert x V) := by
    apply continuousOn_update_iff.mpr
    have diff : insert x V \ {x} = V := by
      ext v
      constructor
      · rintro ⟨eq | mem,ne⟩
        · exact (ne eq).elim
        · exact mem
      · intro mem
        exact ⟨Or.inr mem,fun e => hx (e ▸ mem)⟩
    rw [diff]
    exact ⟨ch,fun _ => hy⟩
  let u := Function.update f p a
  have other : q∉insert p S := by simpa only [mem_insert_iff,not_or] using And.intro ne.symm hq
  have atq : Tendsto u (𝓝[insert p S] q) (𝓝 b) := by
    rw [nhdsWithin_insert_of_ne ne.symm]
    apply qb.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds ne.symm)] with x hx
    exact (Function.update_of_ne hx a f).symm
  refine ⟨Function.update u q b,fill other (fill hp cf pa) atq,?_,?_,Function.update_self ..⟩
  · intro z hz
    have zp : z≠p := fun e => hp (e ▸ hz)
    have zq : z≠q := fun e => hq (e ▸ hz)
    simp [u,Function.update_of_ne zq,Function.update_of_ne zp]
  · rw [Function.update_of_ne ne]
    exact Function.update_self ..

/-- A continuous unit direction on the entire closed square admits a
continuous real phase, including on all four edges and corners. -/
theorem continuous_unit_square_phase {W : unitInterval × unitInterval → ℂ}
    (cW : Continuous W) (unit : ∀ q, ‖W q‖=1) :
    ∃ F : unitInterval × unitInterval → ℝ, Continuous F ∧ ∀ q, exp ((F q:ℂ)*I)=W q := by
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,left_mem_Icc.mpr zero_le_one⟩
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  have nz (q) : W q≠0 := fun e => by simpa only [e,norm_zero,zero_ne_one] using unit q
  let C : C(unitInterval × unitInterval,{v : ℂ // v≠0}) := ⟨fun q => ⟨W q,nz q⟩,cW.subtype_mk _⟩
  obtain ⟨G,⟨_,lift⟩,_⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts C (0,0)
    (W (0,0)).log (Subtype.ext (Complex.exp_log (nz _)))
  refine ⟨fun q => (G q).im,continuous_im.comp G.continuous,fun q => ?_⟩
  have expG : exp (G q)=W q := congrArg Subtype.val (congrFun lift q)
  have reG : (G q).re=0 := (Real.exp_eq_one_iff _).mp (by rw [← Complex.norm_exp,expG,unit])
  have imG : ((G q).im:ℂ)*I=G q := by apply Complex.ext <;> simp [reG]
  rw [imG,expG]

/-- A continuous scalar phase with identically zero sine on a connected
set is one constant integer multiple of π. -/
theorem continuous_phase_sin_zero_constant {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (x : T) {F : T → ℝ} (cF : Continuous F) (zero : ∀ y, Real.sin (F y)=0) :
    ∃ n : ℤ, ∀ y, F y=n*Real.pi := by
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp (zero x)
  refine ⟨n,fun y => ?_⟩
  obtain ⟨m,hm⟩ := Real.sin_eq_zero_iff.mp (zero y)
  have no {k : ℤ} {a b : T} (lo : (k:ℝ)*Real.pi=F a) (hi : ((k:ℝ)+1)*Real.pi≤F b) : False := by
    let v := Real.pi/2+(k:ℝ)*Real.pi
    have inI : v ∈ Icc (F a) (F b) := ⟨by dsimp [v]; linarith [Real.pi_pos],by dsimp [v]; linarith [Real.pi_pos]⟩
    obtain ⟨z,hz⟩ := intermediate_value_univ a b cF inI
    have sin := zero z
    rw [hz,show v=Real.pi/2+(k:ℝ)*Real.pi from rfl,Real.sin_add_int_mul_pi,Real.sin_pi_div_two,mul_one] at sin
    exact (zpow_ne_zero k (by norm_num : (-1:ℝ)≠0)) sin
  rcases lt_trichotomy n m with lt | eq | gt
  · exfalso
    apply no (a := x) (b := y) hn
    rw [← hm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show n+1≤m by omega)) Real.pi_pos.le
  · simpa only [eq] using hm.symm
  · exfalso
    apply no (a := y) (b := x) hm
    rw [← hn]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show m+1≤n by omega)) Real.pi_pos.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.continuous_fill_two_points
#print axioms TwoAxisHelicoid.continuous_unit_square_phase
#print axioms TwoAxisHelicoid.continuous_phase_sin_zero_constant
