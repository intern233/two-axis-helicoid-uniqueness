import TwoAxisHelicoid.EmbeddedTorusSingleSaddleReduction
import TwoAxisHelicoid.SaddleArmOrbitCover
import TwoAxisHelicoid.SingularTorusLevelFlow
import TwoAxisHelicoid.TorusOrbitEndLifts
import TwoAxisHelicoid.TorusSaddleOrbitDirections

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology ContDiff

/-- A single traversal has nonzero lattice displacement, and its two
ends approach adjacent rays of one product chart of the physical
saddle. Every finite point of the traversal has a regular height
chart, including all points of any eventual compact middle segment. -/
def HasSeparatedSaddleReturn (L : PeriodPair) (h : PeriodTorus L → ℝ) : Prop :=
  ∃ (p : PeriodTorus L) (e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ)) (γ : ℝ → ℂ) (a b : ℂ),
    p∈e.source ∧ e p=0 ∧ (∀ᶠ q in 𝓝 p, h q=h p+(e q).1*(e q).2) ∧ h p≠h 0 ∧
    Continuous γ ∧ periodTorusProjection L a=p ∧ periodTorusProjection L b=p ∧ a≠b ∧
    Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b) ∧
    (∀ t, let y := periodTorusProjection L (γ t)
      h y=h p ∧ y≠p ∧ ∃ d : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), y∈d.source ∧
        ∀ w∈d.target, h (d.symm w)=w.2) ∧
    (let f := fun t => e (periodTorusProjection L (γ t))
     ((∀ᶠ t in atTop, (f t).2=0) ∧ ∀ᶠ t in atBot, (f t).1=0) ∨
      ((∀ᶠ t in atTop, (f t).1=0) ∧ ∀ᶠ t in atBot, (f t).2=0))

/-- Extract an actual separated traversal from a nonlifting component
containing a single Morse saddle. The marked torus covering detects
the nonzero period; Hamiltonian orientation forces adjacent arms. -/
theorem marked_single_saddle_has_separated_return (L : PeriodPair) (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    {h : PeriodTorus L → ℝ} (ch : Continuous h)
    (smooth : ∀ z, h (periodTorusProjection L z)≠h 0 → ContDiffAt ℝ ∞ (h ∘ periodTorusProjection L) z)
    (obstruct : HasNonliftingSingleSaddle L H h) : HasSeparatedSaddleReturn L h := by
  obtain ⟨v,x,p,e,diff,inC,src,zero,model,⟨z,zp,sq,iq⟩,critical,fail⟩ := obstruct
  let π := periodTorusProjection L
  let S := h ⁻¹' {v}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_singleton.preimage ch).isCompact
  have crit (w : ℂ) (level : h (π w)=v) :
      (∀ b, fderiv ℝ (h ∘ π) w b=0) ↔ π w=p.1 := by
    rw [← critical w level]
    constructor
    · exact fun all => ContinuousLinearMap.ext (fun b => all b)
    · exact fun eq b => by rw [eq]; rfl
  obtain ⟨G,start,add,cont,op,curves⟩ := singular_torus_level_hamiltonian_action L ch diff smooth p crit
  have failP : ¬∃ u w : C(connectedComponent p,ℝ), ∀ q : connectedComponent p,
      normalizedPhase (u q)=(H q.1.1).1 ∧ normalizedPhase (w q)=(H q.1.1).2 := by
    rw [← connectedComponent_eq inC]
    exact fail
  obtain ⟨y,g,_,gp,gr,_,nonlift⟩ := obstructed_loop_of_saddle_height_action (p:=p.1) p.2
    e src zero model ⟨H,H.continuous⟩ G start add cont op failP
  obtain ⟨γ,sc,_,ode,rep⟩ := curves y
  let g' : C(OnePoint ℝ,PeriodTorus L) := ⟨fun t => (g t).1,continuous_subtype_val.comp g.continuous⟩
  have real (t : ℝ) : g' t=π (γ t) := (congrArg Subtype.val (gr t)).trans (rep t)
  obtain ⟨a,b,atA,atB,apart,al,bl⟩ :=
    obstructed_torus_orbit_has_distinct_plane_ends L γ sc.continuous g' H marked real nonlift
  have point : g' OnePoint.infty=p.1 := congrArg Subtype.val gp
  have ap := atA.trans point
  have bp := atB.trans point
  refine ⟨p.1,e,γ,a,b,src,zero,model,(fun eq => diff (p.2.symm.trans eq)),sc.continuous,ap,bp,apart,al,bl,?_,
    projected_homoclinic_ends_on_adjacent_axes L e zero model zp sq iq ode ap bp al bl⟩
  intro t
  let y' := G t y
  have level : h (π (γ t))=v := (congrArg h (rep t).symm).trans y'.1.2
  have no : π (γ t)≠p.1 := fun eq => y'.2 (Subtype.ext ((rep t).trans eq))
  have nz : fderiv ℝ (h ∘ π) (γ t)≠0 := fun eq => no ((critical _ level).mp eq)
  exact ⟨level.trans p.2.symm,no,torus_height_chart_of_regular_lift L (γ t)
    (smooth _ (fun eq => diff (level.symm.trans eq))) nz⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_single_saddle_has_separated_return
