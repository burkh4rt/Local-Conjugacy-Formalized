module

public import LocalConjugacy.CocycleActions

@[expose] public section

namespace LocalConjugacy
open scoped IsMulCommutative

theorem procyclic_commutative {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (hG : Procyclic G) :
    ∀ x y : G, x * y = y * x := by
  obtain ⟨g, hg⟩ := hG
  have hz : ∀ x ∈ Subgroup.zpowers g, ∀ y : G, x * y = y * x := by
    intro x hx
    have hc : IsClosed {y : G | x * y = y * x} := isClosed_eq
      (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    have hs : (Subgroup.zpowers g : Set G) ⊆ {y : G | x * y = y * x} := by
      intro y hy
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.zpowers g) ⟨y, hy⟩)
    have ht := closure_minimal hs hc
    rw [hg.closure_eq] at ht
    exact fun y => ht (Set.mem_univ y)
  intro x y
  have hc : IsClosed {x : G | x * y = y * x} := isClosed_eq
    (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have ht := closure_minimal (fun z hz' => hz z hz' y) hc
  rw [hg.closure_eq] at ht
  exact ht (Set.mem_univ x)

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The second conclusion of Proposition 2.1 follows from continuity and
coprime orders, for possibly infinite discrete coefficient groups. -/
theorem fixed_cocycle_trivial_on_intersection
    {p q : ℕ} (hpq : p.Coprime q) (hN : IsPGroup p N)
    (K Q : Subgroup J) [K.Normal] (hcyclic : Procyclic Q) (hQ : IsProP q Q)
    (g : Cocycle (N := N) K) (hfix : ∀ x : Q, twistCocycle g x = g) :
    ∀ x ∈ Q, ∀ hx : x ∈ K, g.toFun ⟨x, hx⟩ = 1 := by
  let R := Q ⊓ K
  have ha (x y : R) : (x : J) • g.toFun ⟨y, y.property.2⟩ =
      g.toFun ⟨y, y.property.2⟩ := by
    have he := congrArg (fun f : Cocycle (N := N) K => f.toFun ⟨y, y.property.2⟩)
      (hfix ⟨x, x.property.1⟩)
    change (x : J) • g.toFun ⟨(x : J)⁻¹ * y * x, _⟩ = g.toFun ⟨y, y.property.2⟩ at he
    have hxy := congrArg Subtype.val
      (procyclic_commutative hcyclic (⟨x, x.property.1⟩ : Q) ⟨y, y.property.1⟩)
    change (x : J) * y = (y : J) * x at hxy
    have hc : (x : J)⁻¹ * y * x = y := by rw [mul_assoc, ← hxy]; group
    simpa only [hc] using he
  let φ : R →* N :=
    { toFun := fun x => g.toFun ⟨x, x.property.2⟩
      map_one' := cocycle_one g
      map_mul' := fun x y => by
        change g.toFun ((⟨x, x.property.2⟩ : K) * ⟨y, y.property.2⟩) = _
        rw [g.map_mul, ha x y] }
  have hφ : Continuous φ := g.continuous_toFun.comp
    (continuous_subtype_val.subtype_mk (fun x : R => x.property.2))
  have hR : IsProP q R := isProP_mono inf_le_left hQ
  intro x hx hxK
  exact continuous_hom_eq_one_of_coprime hR hN hpq φ hφ ⟨x, hx, hxK⟩

/-- Proposition 2.1 under the explicit finite-cohomology-class condition.
It also applies to infinite discrete coefficients whenever the class is finite. -/
theorem proposition_2_1_of_finite_class
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f)
    [Finite (CohomologyClass f)] :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨g, hfg, hg⟩ := fixed_cocycle_of_finite_class hne hN Q hpro f hinv
  refine ⟨g, hfg, ?_, ?_⟩
  · intro q hq x hx hqx
    exact congrArg (fun f : Cocycle (N := N) J₀ => f.toFun ⟨x, hx⟩) (hg ⟨q, hq⟩)
  · exact fixed_cocycle_trivial_on_intersection (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hp₀).mp h).symm)) hN J₀ Q hcyclic hpro g hg

end

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false in
/-- Proposition 2.1 with finite discrete coefficient group. -/
theorem proposition_2_1_finite [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 :=
  proposition_2_1_of_finite_class p p₀ hp hp₀ hne hN J₀ Q hcyclic hpro f hinv

end
end LocalConjugacy
