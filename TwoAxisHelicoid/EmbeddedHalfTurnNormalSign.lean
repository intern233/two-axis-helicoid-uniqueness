import TwoAxisHelicoid.EmbeddedRangeInvolution
import TwoAxisHelicoid.RegularChartNormalStability
import TwoAxisHelicoid.SmoothImmersionLeftInverse
import TwoAxisHelicoid.SimilaritySymmetry
import TwoAxisHelicoid.CoordinateSignMaps

namespace TwoAxisHelicoid
open Set Filter Complex Matrix Topology
open scoped Topology ContDiff RealInnerProductSpace

private theorem smooth_chart_contains_curve_velocity {M : Type*} [TopologicalSpace M]
    {Y : M → Fin 3 → ℝ} (hy : IsEmbedding Y) (e : OpenPartialHomeomorph M ℂ) {p : M}
    (hp : p ∈ e.source) (hx : ContDiffAt ℝ ∞ (Y ∘ e.symm) (e p))
    (hi : Function.Injective (fderiv ℝ (Y ∘ e.symm) (e p)))
    {γ : ℝ → Fin 3 → ℝ} {s : ℝ} {v : Fin 3 → ℝ} (hγ : HasDerivAt γ v s)
    (atp : γ s = Y p) (inside : ∀ᶠ t in 𝓝 s, γ t ∈ range Y) :
    ∃ w : ℂ, fderiv ℝ (Y ∘ e.symm) (e p) w = v := by
  let F := Y ∘ e.symm
  have fp : F (e p) = Y p := congrArg Y (e.left_inv hp)
  obtain ⟨τ,U,op,mem,reg,left⟩ := smooth_local_left_inverse hx hi
  have leftNear : ∀ᶠ w in 𝓝 (e p), τ (F w) = w := by
    filter_upwards [op.mem_nhds mem] with w hw
    exact left w hw
  have center : τ (γ s) = e p := by rw [atp,← fp]; exact leftNear.self_of_nhds
  have aτ : DifferentiableAt ℝ τ (γ s) := by
    rw [atp,← fp]
    exact reg.differentiableAt (by simp)
  have good : ∀ᶠ q in 𝓝 p, F (τ (Y q)) = Y q := by
    filter_upwards [e.open_source.mem_nhds hp,(e.continuousAt hp).eventually leftNear] with q hq h
    have val : F (e q) = Y q := congrArg Y (e.left_inv hq)
    rw [← val,h]
  have onImage : ∀ᶠ y in 𝓝[range Y] (Y p), F (τ y) = y := by
    rw [← hy.map_nhds_eq p]; exact good
  have tend : Tendsto γ (𝓝 s) (𝓝[range Y] (Y p)) :=
    tendsto_nhdsWithin_iff.mpr ⟨atp ▸ hγ.continuousAt.tendsto,inside⟩
  have eq : F ∘ (τ ∘ γ) =ᶠ[𝓝 s] γ := tend.eventually onImage
  have d := aτ.hasFDerivAt.comp_hasDerivAt s hγ
  have af : DifferentiableAt ℝ F (τ (γ s)) := center.symm ▸ hx.differentiableAt (by simp)
  have actual : fderiv ℝ F (τ (γ s)) (fderiv ℝ τ (γ s) v) = v :=
    ((af.hasFDerivAt.comp_hasDerivAt s d).congr_of_eventuallyEq eq.symm).unique hγ
  exact ⟨fderiv ℝ τ (γ s) v,by simpa only [center] using actual⟩

private theorem cartesian_inner_normal (a b : Fin 3 → ℝ) :
    ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫ = a ⬝ᵥ b := by
  rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,
    star_trivial,dotProduct_comm]

private theorem cartesian_unit_normal {n : Fin 3 → ℝ} (hu : n ⬝ᵥ n = 1) :
    ‖coordinateToEuclidean n‖ = 1 := by
  have h : ‖coordinateToEuclidean n‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq,cartesian_inner_normal,hu]
  nlinarith [norm_nonneg (coordinateToEuclidean n)]

/-- A half-turn which preserves a connected embedded regular surface and whose
axis lies on it reverses every continuous choice of unit normal.  The tangent
action is derived from actual curves on the surface. -/
theorem embedded_half_turn_reverses_unit_normal {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    {Y : M → Fin 3 → ℝ} (hy : IsEmbedding Y) (e : M → OpenPartialHomeomorph M ℂ)
    (center : ∀ p, p ∈ (e p).source) (smooth : ∀ p, ContDiffAt ℝ ∞ (Y ∘ (e p).symm) (e p p))
    (imm : ∀ p, Function.Injective (fderiv ℝ (Y ∘ (e p).symm) (e p p)))
    {N : M → Fin 3 → ℝ} (cn : Continuous N) (unit : ∀ p, N p ⬝ᵥ N p = 1)
    (normal : ∀ p v, fderiv ℝ (Y ∘ (e p).symm) (e p p) v ⬝ᵥ N p = 0)
    (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (inv : Function.Involutive R)
    (orth : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b) (sym : ∀ p, R (Y p) ∈ range Y)
    (axis : Fin 3 → ℝ) (line : ∀ t : ℝ, t • axis ∈ range Y)
    (turn : ∀ n, axis ⬝ᵥ n = 0 → R n = -n) :
    ∀ p q, Y q = R (Y p) → N q = -R (N p) := by
  let d := embeddedRangeInvolution hy R R.continuous inv sym
  have acts (p : M) : Y (d p) = R (Y p) := embeddedRangeInvolution_eq hy R R.continuous inv sym p
  let D := fun p => fderiv ℝ (Y ∘ (e p).symm) (e p p)
  have carry (p : M) (v : ℂ) : ∃ w : ℂ, D (d p) w = R (D p v) := by
    let F := Y ∘ (e p).symm
    let l := fun t : ℝ => e p p + t • v
    have l0 : l 0 = e p p := by simp [l]
    have dl : HasDerivAt l v 0 := by
      simpa only [l,id_eq,zero_add,one_smul] using
        (hasDerivAt_const (0:ℝ) (e p p)).fun_add ((hasDerivAt_id (0:ℝ)).smul_const v)
    have df : HasFDerivAt F (D p) (l 0) := l0.symm ▸ ((smooth p).differentiableAt (by simp)).hasFDerivAt
    have dv := R.hasFDerivAt.comp_hasDerivAt 0 (df.comp_hasDerivAt 0 dl)
    apply smooth_chart_contains_curve_velocity hy (e (d p)) (center _) (smooth _) (imm _) dv
    · change R (Y ((e p).symm (l 0))) = Y (d p)
      rw [l0,(e p).left_inv (center p),acts]
    · exact Eventually.of_forall fun t => sym ((e p).symm (l t))
  let n := fun p => R (N (d p))
  have cont : Continuous n := R.continuous.comp (cn.comp d.continuous)
  have signs (p : M) : n p = N p ∨ n p = -N p := by
    let T := coordinateToEuclidean.comp (D p)
    have inj : Function.Injective T := surfaceCartesianEquiv.symm.injective.comp (imm p)
    have un : n p ⬝ᵥ n p = 1 := (orth _ _).trans (unit (d p))
    have pn (v : ℂ) : ⟪T v,coordinateToEuclidean (N p)⟫ = 0 :=
      (cartesian_inner_normal _ _).trans (normal p v)
    have pm (v : ℂ) : ⟪T v,coordinateToEuclidean (n p)⟫ = 0 := by
      obtain ⟨w,hw⟩ := carry p v
      change ⟪coordinateToEuclidean (D p v),coordinateToEuclidean (R (N (d p)))⟫ = 0
      rw [cartesian_inner_normal,← orth (D p v) (R (N (d p))),inv,← hw]
      exact normal (d p) w
    rcases regular_plane_unit_normal_choices inj (cartesian_unit_normal (unit p))
      (cartesian_unit_normal un) pn pm with h|h
    · exact Or.inl (surfaceCartesianEquiv.symm.injective h)
    · right
      apply (show Function.Injective coordinateToEuclidean from surfaceCartesianEquiv.symm.injective)
      simpa only [map_neg] using h
  obtain ⟨p₀,pos⟩ := line 0
  have zero : Y p₀ = 0 := by simpa using pos
  have fixed : d p₀ = p₀ := hy.injective ((acts p₀).trans (by rw [zero,map_zero]))
  have dl : HasDerivAt (fun t : ℝ => t • axis) axis 0 := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const axis
  obtain ⟨v,hv⟩ := smooth_chart_contains_curve_velocity hy (e p₀) (center _) (smooth _) (imm _) dl
    (by simpa using zero.symm) (Eventually.of_forall line)
  have seed : n p₀ = -N p₀ := by
    change R (N (d p₀)) = -N p₀
    rw [fixed]
    exact turn _ (hv ▸ normal p₀ v)
  let P : Set M := {p | n p = -N p}
  have closed : IsClosed P := isClosed_eq cont cn.neg
  have compl : Pᶜ = {p | n p = N p} := by
    ext p
    change (¬ n p = -N p) ↔ n p = N p
    constructor
    · exact fun h => (signs p).resolve_right h
    · intro plus neg
      have contra : N p ⬝ᵥ N p = N p ⬝ᵥ -N p := congrArg (fun a => N p ⬝ᵥ a) (plus.symm.trans neg)
      rw [dotProduct_neg,unit] at contra
      linarith
  have op : IsOpen P := isClosed_compl_iff.mp (by rw [compl]; exact isClosed_eq cont cn)
  have all := (show IsClopen P from ⟨closed,op⟩).eq_univ ⟨p₀,seed⟩
  intro p q hq
  have same : q = d p := hy.injective (hq.trans (acts p).symm)
  rw [same]
  have mem : p ∈ P := by rw [all]; exact mem_univ p
  have h : R (R (N (d p))) = R (-N p) := congrArg R (show n p = -N p from mem)
  simpa only [inv _,map_neg] using h

/-- Both coordinate half-turns act with the negative normal sign on a
connected embedded surface containing the two actual straight lines. -/
theorem embedded_coordinate_half_turn_normal_signs {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    {Y : M → Fin 3 → ℝ} (hy : IsEmbedding Y) (e : M → OpenPartialHomeomorph M ℂ)
    (center : ∀ p, p ∈ (e p).source) (smooth : ∀ p, ContDiffAt ℝ ∞ (Y ∘ (e p).symm) (e p p))
    (imm : ∀ p, Function.Injective (fderiv ℝ (Y ∘ (e p).symm) (e p p)))
    {N : M → Fin 3 → ℝ} (cn : Continuous N) (unit : ∀ p, N p ⬝ᵥ N p = 1)
    (normal : ∀ p v, fderiv ℝ (Y ∘ (e p).symm) (e p p) v ⬝ᵥ N p = 0)
    (sym : ∀ p, halfTurnX (Y p) ∈ range Y ∧ halfTurnZ (Y p) ∈ range Y)
    (lineX : ∀ t : ℝ, (![t,0,0] : Fin 3 → ℝ) ∈ range Y)
    (lineZ : ∀ t : ℝ, (![0,0,t] : Fin 3 → ℝ) ∈ range Y) :
    (∀ p q, Y q = halfTurnX (Y p) → N q = -halfTurnX (N p)) ∧
    (∀ p q, Y q = halfTurnZ (Y p) → N q = -halfTurnZ (N p)) := by
  let Rx := coordinateSignMap (![1,-1,-1] : Fin 3 → ℝ)
  let Rz := coordinateSignMap (![-1,-1,1] : Fin 3 → ℝ)
  have hx (v : Fin 3 → ℝ) : Rx v = halfTurnX v := by ext i; fin_cases i <;> simp [Rx,halfTurnX]
  have hz (v : Fin 3 → ℝ) : Rz v = halfTurnZ v := by ext i; fin_cases i <;> simp [Rz,halfTurnZ]
  have ix : Function.Involutive Rx := coordinateSignMap_involutive (by intro i; fin_cases i <;> norm_num)
  have iz : Function.Involutive Rz := coordinateSignMap_involutive (by intro i; fin_cases i <;> norm_num)
  have ox (v w : Fin 3 → ℝ) : Rx v ⬝ᵥ Rx w = v ⬝ᵥ w := by simp [hx,halfTurnX,dotProduct,Fin.sum_univ_succ]
  have oz (v w : Fin 3 → ℝ) : Rz v ⬝ᵥ Rz w = v ⬝ᵥ w := by simp [hz,halfTurnZ,dotProduct,Fin.sum_univ_succ]
  have lx (t : ℝ) : t • (![1,0,0] : Fin 3 → ℝ) ∈ range Y := by
    have h : t • (![1,0,0] : Fin 3 → ℝ) = ![t,0,0] := by ext i; fin_cases i <;> simp
    rw [h]; exact lineX t
  have lz (t : ℝ) : t • (![0,0,1] : Fin 3 → ℝ) ∈ range Y := by
    have h : t • (![0,0,1] : Fin 3 → ℝ) = ![0,0,t] := by ext i; fin_cases i <;> simp
    rw [h]; exact lineZ t
  have tx (n : Fin 3 → ℝ) (h : ![1,0,0] ⬝ᵥ n = 0) : Rx n = -n := by
    have h₀ : n 0 = 0 := by simpa [dotProduct,Fin.sum_univ_succ] using h
    ext i; fin_cases i <;> simp [Rx,h₀]
  have tz (n : Fin 3 → ℝ) (h : ![0,0,1] ⬝ᵥ n = 0) : Rz n = -n := by
    have h₂ : n 2 = 0 := by simpa [dotProduct,Fin.sum_univ_succ] using h
    ext i; fin_cases i <;> simp [Rz,h₂]
  constructor
  · simpa only [hx] using embedded_half_turn_reverses_unit_normal hy e center smooth imm cn unit normal
      Rx ix ox (fun p => by rw [hx]; exact (sym p).1) _ lx tx
  · simpa only [hz] using embedded_half_turn_reverses_unit_normal hy e center smooth imm cn unit normal
      Rz iz oz (fun p => by rw [hz]; exact (sym p).2) _ lz tz

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_half_turn_reverses_unit_normal
#print axioms TwoAxisHelicoid.embedded_coordinate_half_turn_normal_signs
