import TwoAxisHelicoid.DisjointTorusCoreObstruction
import TwoAxisHelicoid.OrderedCoreSections

namespace TwoAxisHelicoid
open Set Topology

/-- Two open torus cores whose limiting slabs differ by two screw
periods cannot both occur in an approximating singly punctured torus.
Only the vertical positions of the two parametrizations need to be
close to their limits. -/
theorem twice_translated_slabs_cannot_both_approximate_a_torus
    {A L : PeriodPair} (C : TorusGeneratingCoreModel A) {h : ℝ} (_hh : 0 < h)
    (height : C.carrier → ℝ) (hslab : ∀ x, height x ∈ Ioo (-h) h)
    (Y : PeriodTorus L → Fin 3 → ℝ) (f g : C.carrier → PeriodTorus L)
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (herr : ∀ x, |Y (f x) 2-height x| < h)
    (herr' : ∀ x, |Y (g x) 2-(height x+4*h)| < h) : False := by
  apply disjoint_genus_one_cores_impossible C C f g hf hg
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,rfl⟩ ⟨y,he⟩
  have h₁ := (abs_lt.mp (herr x)).2
  have h₂ := (abs_lt.mp (herr' y)).1
  rw [he] at h₂
  linarith [(hslab x).2,(hslab y).1]

/-- A local finite normal cover on each of the two separated compact
cores already contradicts genus one of the approximating surfaces.
Neither local convergence nor either covering is assumed single sheet. -/
theorem periodic_core_limit_excluded_of_ordered_normal_covers
    {A L : PeriodPair} (C : TorusGeneratingCoreModel A) {h : ℝ} (hh : 0 < h)
    (height : C.carrier → ℝ) (hslab : ∀ x, height x ∈ Ioo (-h) h)
    (Y : PeriodTorus L → Fin 3 → ℝ) {E D : Type*} [TopologicalSpace E] [TopologicalSpace D]
    (j : E → PeriodTorus L) (i : D → PeriodTorus L) (hj : IsOpenEmbedding j) (hi : IsOpenEmbedding i)
    {p : E → C.carrier} {q : D → C.carrier} (hp : IsProperMap p) (hq : IsProperMap q)
    (lp : IsLocalHomeomorph p) (lq : IsLocalHomeomorph q) (sp : Function.Surjective p) (sq : Function.Surjective q)
    {u : E → ℝ} {v : D → ℝ} (hu : Continuous u) (hv : Continuous v)
    (su : ∀ a b, p a = p b → u a = u b → a = b) (sv : ∀ a b, q a = q b → v a = v b → a = b)
    (herr : ∀ z, |Y (j z) 2-height (p z)| < h)
    (herr' : ∀ z, |Y (i z) 2-(height (q z)+4*h)| < h) : False := by
  obtain ⟨f,hf,hF,_⟩ := lowest_fiber_open_section hp lp sp hu su
  obtain ⟨g,hg,hG,_⟩ := lowest_fiber_open_section hq lq sq hv sv
  exact twice_translated_slabs_cannot_both_approximate_a_torus C hh height hslab Y (j ∘ f) (i ∘ g)
    (hj.comp hf) (hi.comp hg) (fun x => by simpa only [Function.comp_apply,hF] using herr (f x))
    (fun x => by simpa only [Function.comp_apply,hG] using herr' (g x))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_core_limit_excluded_of_ordered_normal_covers
