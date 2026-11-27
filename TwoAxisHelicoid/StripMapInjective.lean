import TwoAxisHelicoid.ImplicitScalarDerivative
import TwoAxisHelicoid.ScalarBivariateDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

theorem surjective_of_derivative_lower_bound {f f' : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hd : ∀ x, HasDerivAt f (f' x) x) (hl : ∀ x, c ≤ f' x) :
    Function.Surjective f := by
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hlow : ∀ x, c ≤ deriv f x := fun x => by rw [(hd x).deriv]; exact hl x
  intro u
  let L := (|u-f 0|+1)/c
  have hL : 0 ≤ L := le_of_lt (div_pos (by positivity) hc)
  have hcL : c*L = |u-f 0|+1 := by dsimp [L]; field_simp
  have hp := mul_sub_le_image_sub_of_le_deriv hdiff hlow hL
  have hn := mul_sub_le_image_sub_of_le_deriv hdiff hlow (neg_nonpos.mpr hL)
  apply mem_range_of_exists_le_of_exists_ge hdiff.continuous
  · exact ⟨-L,by nlinarith [neg_abs_le (u-f 0)]⟩
  · exact ⟨L,by nlinarith [le_abs_self (u-f 0)]⟩

/-- Continuity of the inverse of a family of increasing bijections, with only
pointwise continuity in the parameter needed. -/
theorem increasing_family_inverse_continuousAt {F : ℝ → ℝ → ℝ} {l h s u : ℝ}
    (hs : s ∈ Ioo l h)
    (hmono : ∀ t ∈ Ioo l h, StrictMono (F t))
    (hsurj : ∀ t ∈ Ioo l h, Function.Surjective (F t))
    (hcont : ∀ r, ContinuousAt (fun t => F t r) s) :
    ContinuousAt (fun t => Function.invFun (F t) u) s := by
  let a := fun t => Function.invFun (F t) u
  have ha (t : ℝ) (ht : t ∈ Ioo l h) : F t (a t) = u :=
    Function.rightInverse_invFun (hsurj t ht) u
  change ContinuousAt a s
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hb' : F s b < u := by rw [← ha s hs]; exact hmono s hs hb
    have he := (hcont b).eventually (eventually_lt_nhds hb')
    filter_upwards [he,Ioo_mem_nhds hs.1 hs.2] with t ht htI
    by_contra hn
    have hh := (hmono t htI).monotone (le_of_not_gt hn)
    rw [ha t htI] at hh
    linarith
  · intro b hb
    have hb' : u < F s b := by rw [← ha s hs]; exact hmono s hs hb
    have he := (hcont b).eventually (eventually_gt_nhds hb')
    filter_upwards [he,Ioo_mem_nhds hs.1 hs.2] with t ht htI
    by_contra hn
    have hh := (hmono t htI).monotone (le_of_not_gt hn)
    rw [ha t htI] at hh
    linarith

/-- A planar strip map is injective when its first coordinate is an increasing
bijection on every horizontal line and its Jacobian is strictly negative.
All smoothness, derivative signs, and surjectivity are explicit hypotheses. -/
theorem strip_map_injective {F G Fs Fr Gs Gr : ℝ → ℝ → ℝ} {l h : ℝ}
    (hFs : ∀ s r, HasDerivAt (fun t => F t r) (Fs s r) s)
    (hFr : ∀ s r, HasDerivAt (F s) (Fr s r) r)
    (hGs : ∀ s r, HasDerivAt (fun t => G t r) (Gs s r) s)
    (hGr : ∀ s r, HasDerivAt (G s) (Gr s r) r)
    (hcFs : Continuous (fun p : ℝ × ℝ => Fs p.1 p.2))
    (hcFr : Continuous (fun p : ℝ × ℝ => Fr p.1 p.2))
    (hcGs : Continuous (fun p : ℝ × ℝ => Gs p.1 p.2))
    (hcGr : Continuous (fun p : ℝ × ℝ => Gr p.1 p.2))
    (hpos : ∀ s ∈ Ioo l h, ∀ r, 0 < Fr s r)
    (hsurj : ∀ s ∈ Ioo l h, Function.Surjective (F s))
    (hjac : ∀ s ∈ Ioo l h, ∀ r, Fr s r*Gs s r-Fs s r*Gr s r < 0) :
    Set.InjOn (fun p : ℝ × ℝ => (F p.1 p.2,G p.1 p.2)) (Ioo l h ×ˢ univ) := by
  have hmono (s : ℝ) (hs : s ∈ Ioo l h) : StrictMono (F s) :=
    strictMono_of_hasDerivAt_pos (hFr s) (hpos s hs)
  intro p hp q hq heq
  have hF : F p.1 p.2 = F q.1 q.2 := congrArg Prod.fst heq
  have hG : G p.1 p.2 = G q.1 q.2 := congrArg Prod.snd heq
  let u := F p.1 p.2
  let a := fun s => Function.invFun (F s) u
  have ha (s : ℝ) (hs : s ∈ Ioo l h) : F s (a s) = u :=
    Function.rightInverse_invFun (hsurj s hs) u
  have hap : a p.1 = p.2 := (hmono p.1 hp.1).injective (ha p.1 hp.1)
  have haq : a q.1 = q.2 := (hmono q.1 hq.1).injective ((ha q.1 hq.1).trans hF)
  have hader (s : ℝ) (hs : s ∈ Ioo l h) :
      HasDerivAt a (-Fs s (a s)/Fr s (a s)) s := by
    apply implicit_scalar_hasDerivAt (F := fun t r => F t r-u)
    · exact Eventually.of_forall (fun p => (hFs p.1 p.2).sub_const u)
    · exact Eventually.of_forall (fun p => (hFr p.1 p.2).sub_const u)
    · exact hcFs.continuousAt
    · exact hcFr.continuousAt
    · exact (hpos s hs (a s)).ne'
    · exact increasing_family_inverse_continuousAt hs hmono hsurj
        (fun r => (hFs s r).continuousAt)
    · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact sub_eq_zero.mpr (ha t ht)
  have hder (s : ℝ) (hs : s ∈ Ioo l h) :
      HasDerivAt (fun t => G t (a t))
        (Gs s (a s)+(-Fs s (a s)/Fr s (a s))*Gr s (a s)) s := by
    simpa only [one_mul, id_eq] using scalar_bivariate_curve_hasDerivAt
      (Eventually.of_forall (fun p => hGs p.1 p.2))
      (Eventually.of_forall (fun p => hGr p.1 p.2))
      hcGs.continuousAt hcGr.continuousAt (hasDerivAt_id s) (hader s hs)
  have hanti : StrictAntiOn (fun s => G s (a s)) (Ioo l h) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo l h)
    · exact fun s hs => (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo l h := interior_subset hs
      rw [(hder s hs').deriv]
      have hfr := hpos s hs' (a s)
      have hj := hjac s hs' (a s)
      have he : Gs s (a s)+(-Fs s (a s)/Fr s (a s))*Gr s (a s) =
          (Fr s (a s)*Gs s (a s)-Fs s (a s)*Gr s (a s))/Fr s (a s) := by
        field_simp
        ring
      rw [he]
      exact div_neg_of_neg_of_pos hj hfr
  have hfirst : p.1 = q.1 := hanti.injOn hp.1 hq.1 (by simpa only [hap,haq] using hG)
  apply Prod.ext hfirst
  apply (hmono p.1 hp.1).injective
  simpa only [← hfirst] using hF

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.strip_map_injective
