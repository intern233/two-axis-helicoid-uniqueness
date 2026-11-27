import TwoAxisHelicoid.OneEndThinGraph
import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.HelicoidGraphDerivative

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff

/-- Injectivity of the derivative of the actual normal projection,
away from some compact set. No angle or lower singular value is prescribed. -/
def NoncriticalHelicoidEndProjection {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → HelicoidTubeCoordinates) : Prop :=
  ∀ᶠ q in cocompact M, Function.Injective
    (fderiv ℝ (helicoidBaseCoordinates ∘ X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q))

private theorem projection_inverse_at_regular_point {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {q : M} {c : OpenPartialHomeomorph M ℂ} (inside : q∈c.source)
    (smooth : ContDiffAt ℝ ∞ (X ∘ c.symm) (c q)) (tube : X q∈helicoidTubeEquiv.target)
    (noncritical : Function.Injective (fderiv ℝ (helicoidBaseCoordinates ∘ X ∘ c.symm) (c q))) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ), q∈e.source ∧ EqOn (helicoidBaseCoordinates ∘ X) e e.source ∧
      ContDiffAt ℝ ∞ (X ∘ e.symm) (helicoidBaseCoordinates (X q)) := by
  let p := helicoidBaseCoordinates ∘ X ∘ c.symm
  have atq : (X ∘ c.symm) (c q)=X q := congrArg X (c.left_inv inside)
  have sp : ContDiffAt ℝ ∞ p (c q) :=
    (helicoidBaseCoordinates_contDiffAt (atq.symm ▸ tube)).comp (c q) smooth
  let D := fderiv ℝ p (c q)
  let E := (D.toLinearMap.linearEquivOfInjective noncritical
    Complex.equivRealProdCLM.toLinearEquiv.finrank_eq).toContinuousLinearEquiv
  have hd : HasFDerivAt p (E : ℂ →L[ℝ] (ℝ × ℝ)) (c q) := (sp.differentiableAt (by simp)).hasFDerivAt
  let d := sp.toOpenPartialHomeomorph p hd (by simp)
  have contains : c q∈d.source := sp.mem_toOpenPartialHomeomorph_source hd (by simp)
  have val : d (c q)=helicoidBaseCoordinates (X q) := congrArg helicoidBaseCoordinates atq
  have back : d.symm (helicoidBaseCoordinates (X q))=c q := by rw [← val]; exact d.left_inv contains
  refine ⟨c.trans d,⟨inside,contains⟩,?_,?_⟩
  · intro x hx
    change helicoidBaseCoordinates (X x)=helicoidBaseCoordinates (X (c.symm (c x)))
    rw [c.left_inv hx.1]
  · change ContDiffAt ℝ ∞ ((X ∘ c.symm) ∘ d.symm) (helicoidBaseCoordinates (X q))
    rw [← val]
    exact (show ContDiffAt ℝ ∞ (X ∘ c.symm) (d.symm (d (c q))) by rwa [d.left_inv contains]).comp _
      (sp.to_localInverse hd (by simp))

/-- In an arbitrarily thin helicoid tube a one-ended proper embedding
is a single smooth graph of decaying height as soon as its projection
has no critical point outside a compact set. Transversality may
degenerate along a sequence of points going to infinity. -/
theorem height_graph_from_noncritical_projection {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    {X : M → HelicoidTubeCoordinates} (proper : IsProperMap X) (inj : Function.Injective X)
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    (smooth : ∀ q, ContDiffAt ℝ ∞ (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q))
    (thin : ∀ ε : ℝ, 0<ε → ∃ K : Set M, IsCompact K ∧ ∀ q∉K,
      X q∈helicoidTubeEquiv.target ∧ |helicoidSignedDistance (X q)|≤ε)
    (noncritical : NoncriticalHelicoidEndProjection X) : HasHelicoidHeightEnd X := by
  obtain ⟨K₁,compact₁,thin₁⟩ := thin (1/2) (by norm_num)
  obtain ⟨K₂,compact₂,off⟩ := mem_cocompact'.mp noncritical
  let K := K₁ ∪ K₂
  have compact : IsCompact K := compact₁.union compact₂
  have inside (q) (h : q∉K) := thin₁ q (fun hq => h (Or.inl hq))
  have point (q) (h : q∉K) := projection_inverse_at_regular_point (mem_chart_source ℂ q)
    (smooth q) (inside q h).1 (by
      by_contra no
      exact h (Or.inr (off no)))
  have localProjection : IsLocalHomeomorphOn (helicoidBaseCoordinates ∘ X) Kᶜ := by
    apply IsLocalHomeomorphOn.mk
    intro q hq
    obtain ⟨e,mem,eq,_⟩ := point q hq
    exact ⟨e,mem,eq⟩
  obtain ⟨R,rp,core,e,proj,u,_,formula⟩ := helicoid_one_end_exterior_graph tail proper inj.injOn compact
    (by norm_num : (1/2:ℝ)<1) (fun q h => (inside q h).1) (fun q h => (inside q h).2) localProjection
  have base (q : helicoidProjectedEnd X K (exteriorPlaneBase R)) : (e q).1=helicoidBaseCoordinates (X q.1) := by
    rw [proj]; rfl
  have value (b : exteriorPlaneBase R) : u b=helicoidSignedDistance (X (e.symm b).1) := by
    rw [(formula b).2]
    exact (helicoidSignedDistance_on_normal (show ((u b,b.1.1),b.1.2)∈helicoidTubeStrip from
      (formula b).1.trans_lt (by norm_num))).symm
  refine ⟨_,core,R,rp,e,u,?_,fun b => (formula b).1,fun q => ?_,?_⟩
  · apply contDiffOn_extendOpenScalar_of_smooth_germs (exteriorPlaneBase_isOpen R)
    apply helicoid_graph_height_has_smooth_germs e base value (fun q => (inside _ q.2.1).1)
    intro q
    simpa only [base,Function.comp_def] using point q.1 q.2.1
  · simpa only [e.symm_apply_apply] using (formula (e q)).2
  · have lim := helicoid_graph_height_tendsto_zero proper.continuous (by norm_num : (1/2:ℝ)<1)
        (fun b => (formula b).1) (fun b => (formula b).2) (by
          intro δ pos
          obtain ⟨C,kc,bound⟩ := thin (δ/2) (by positivity)
          exact ⟨C,kc,fun q h => ((bound q h).2).trans_lt (by linarith)⟩)
    simpa only [Function.comp_def,abs_zero] using (continuous_abs.tendsto 0).comp lim

/-- Conversely the graph formula and regularity of the actual immersion
force its true projection derivative to have zero kernel. -/
theorem HasHelicoidHeightEnd.noncritical_projection {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidHeightEnd X)
    (regular : ∀ q, DifferentiableAt ℝ (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) ∧
      Function.Injective (fderiv ℝ (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q))) :
    NoncriticalHelicoidEndProjection X := by
  obtain ⟨S,core,R,_,E,u,smooth,bound,formula,_⟩ := graph
  let U := extendOpenScalar u
  have os : IsOpen S := by simpa only [compl_compl] using core.isClosed.isOpen_compl
  have coordinate (q : S) : helicoidBaseCoordinates (X q.1)=(E q).1 := by
    rw [formula q]
    exact normal_graph_coordinates_exact ((bound _).trans_lt (by norm_num)) _
  have graphAt (q : S) : X q.1=helicoidGraphMap U (helicoidBaseCoordinates (X q.1)) := by
    rw [coordinate]
    simpa only [helicoidGraphMap,U,extendOpenScalar,dite_eq_left (E q).2] using formula q
  have tail : S∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  filter_upwards [tail] with q hq
  let c := chartAt ℂ q
  let Z := X ∘ c.symm
  let P := helicoidBaseCoordinates ∘ Z
  have qc : q∈c.source := mem_chart_source ℂ q
  have atq : Z (c q)=X q := congrArg X (c.left_inv qc)
  have fact : Z=ᶠ[𝓝 (c q)] helicoidGraphMap U ∘ P := by
    have nb : ∀ᶠ z in 𝓝 (c q), c.symm z∈S := by
      apply (c.continuousAt_symm (c.map_source qc)).eventually
      rw [c.left_inv qc]
      exact os.mem_nhds hq
    exact nb.mono (fun z hz => graphAt ⟨c.symm z,hz⟩)
  let b := E ⟨q,hq⟩
  have pb : P (c q)=b.1 := (congrArg helicoidBaseCoordinates atq).trans (coordinate ⟨q,hq⟩)
  have tube : X q∈helicoidTubeEquiv.target := by
    rw [formula ⟨q,hq⟩]
    exact helicoidTubeEquiv.map_source ((bound b).trans_lt (by norm_num))
  have dP : DifferentiableAt ℝ P (c q) := ((helicoidBaseCoordinates_contDiffAt (atq.symm ▸ tube)).differentiableAt
    (by simp)).comp (c q) (regular q).1
  have dU : DifferentiableAt ℝ U (P (c q)) := by
    rw [pb]
    exact (smooth.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds b.2)).differentiableAt (by simp)
  have dZ := fact.fderiv_eq.trans (fderiv_comp (c q) (helicoidGraphMap_differentiableAt dU) dP)
  intro v w eq
  apply (regular q).2
  change fderiv ℝ Z (c q) v=fderiv ℝ Z (c q) w
  rw [dZ]
  exact congrArg (fderiv ℝ (helicoidGraphMap U) (P (c q))) eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_graph_from_noncritical_projection
#print axioms TwoAxisHelicoid.HasHelicoidHeightEnd.noncritical_projection
