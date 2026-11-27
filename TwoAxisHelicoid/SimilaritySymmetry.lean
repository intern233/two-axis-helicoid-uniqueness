import TwoAxisHelicoid.SimilarityFieldRigidity

set_option autoImplicit false
namespace TwoAxisHelicoid
open Matrix

noncomputable def halfTurnX (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![v 0,-v 1,-v 2]
noncomputable def halfTurnZ (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![-v 0,-v 1,v 2]

noncomputable def similarityNormal {M : Type*} (X N : M → Fin 3 → ℝ)
    (a b : Fin 3 → ℝ) (d : ℝ) (p : M) : ℝ :=
  ∑ j, similarityField a b d (X p) j*N p j

theorem halfTurns_common_fixed_vector {v : Fin 3 → ℝ}
    (hx : halfTurnX v = v) (hz : halfTurnZ v = v) : v = 0 := by
  have h₀ := congrFun hz 0
  have h₁ := congrFun hx 1
  have h₂ := congrFun hx 2
  dsimp [halfTurnX,halfTurnZ] at h₀ h₁ h₂
  ext j
  fin_cases j <;> dsimp <;> linarith

theorem similarityNormal_sub {M : Type*} (X N : M → Fin 3 → ℝ)
    (a b a' b' : Fin 3 → ℝ) (d d' : ℝ) (p : M) :
    similarityNormal X N (a-a') (b-b') (d-d') p =
      similarityNormal X N a b d p-similarityNormal X N a' b' d' p := by
  simp [similarityNormal,similarityField,Fin.sum_univ_succ,crossProduct]
  ring

theorem similarityNormal_halfTurnX {M : Type*} {X N : M → Fin 3 → ℝ} {ρ : M → M}
    (hX : ∀ p, X (ρ p) = halfTurnX (X p))
    (hN : ∀ p, N (ρ p) = -halfTurnX (N p))
    (a b : Fin 3 → ℝ) (d : ℝ) (p : M) :
    similarityNormal X N a b d (ρ p) =
      -similarityNormal X N (halfTurnX a) (halfTurnX b) d p := by
  simp [similarityNormal,similarityField,hX,hN,halfTurnX,Fin.sum_univ_succ,crossProduct]
  dsimp [vecHead,vecTail]
  ring

theorem similarityNormal_halfTurnZ {M : Type*} {X N : M → Fin 3 → ℝ} {ρ : M → M}
    (hX : ∀ p, X (ρ p) = halfTurnZ (X p))
    (hN : ∀ p, N (ρ p) = -halfTurnZ (N p))
    (a b : Fin 3 → ℝ) (d : ℝ) (p : M) :
    similarityNormal X N a b d (ρ p) =
      -similarityNormal X N (halfTurnZ a) (halfTurnZ b) d p := by
  simp [similarityNormal,similarityField,hX,hN,halfTurnZ,Fin.sum_univ_succ,crossProduct]
  dsimp [vecHead,vecTail]
  ring

/-- Appendix D.2's consequence of independence of the seven normal fields:
actual odd half-turn symmetries remove all translation and rotation
coefficients. The independence premise is explicit and remains geometric. -/
theorem two_axis_odd_similarity_normal_only_dilation
    {M : Type*} {X N : M → Fin 3 → ℝ} {ρX ρZ : M → M}
    (hXX : ∀ p, X (ρX p) = halfTurnX (X p))
    (hNX : ∀ p, N (ρX p) = -halfTurnX (N p))
    (hXZ : ∀ p, X (ρZ p) = halfTurnZ (X p))
    (hNZ : ∀ p, N (ρZ p) = -halfTurnZ (N p))
    (hker : ∀ a b d, (∀ p, similarityNormal X N a b d p = 0) → a = 0 ∧ b = 0 ∧ d = 0)
    {a b : Fin 3 → ℝ} {d : ℝ}
    (hoddX : ∀ p, similarityNormal X N a b d (ρX p) = -similarityNormal X N a b d p)
    (hoddZ : ∀ p, similarityNormal X N a b d (ρZ p) = -similarityNormal X N a b d p) :
    a = 0 ∧ b = 0 := by
  have hfX : ∀ p, similarityNormal X N (halfTurnX a) (halfTurnX b) d p =
      similarityNormal X N a b d p := by
    intro p
    exact neg_injective ((similarityNormal_halfTurnX hXX hNX a b d p).symm.trans (hoddX p))
  have hfZ : ∀ p, similarityNormal X N (halfTurnZ a) (halfTurnZ b) d p =
      similarityNormal X N a b d p := by
    intro p
    exact neg_injective ((similarityNormal_halfTurnZ hXZ hNZ a b d p).symm.trans (hoddZ p))
  have hkX := hker (halfTurnX a-a) (halfTurnX b-b) (d-d) (by
    intro p
    rw [similarityNormal_sub,hfX,sub_self])
  have hkZ := hker (halfTurnZ a-a) (halfTurnZ b-b) (d-d) (by
    intro p
    rw [similarityNormal_sub,hfZ,sub_self])
  exact ⟨halfTurns_common_fixed_vector (sub_eq_zero.mp hkX.1) (sub_eq_zero.mp hkZ.1),
    halfTurns_common_fixed_vector (sub_eq_zero.mp hkX.2.1) (sub_eq_zero.mp hkZ.2.1)⟩

theorem fixed_nonzero_pitch_kills_dilation {pitch d : ℝ}
    (hp : pitch ≠ 0) (hd : d*pitch = 0) : d = 0 := (mul_eq_zero.mp hd).resolve_right hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.two_axis_odd_similarity_normal_only_dilation
