module

public import LocalConjugacy.Counterexamples.QuaternionMatrix
public import LocalConjugacy.FiniteSylow
public import LocalConjugacy.Conjugation
public import LocalConjugacy.ExampleDefinitions

@[expose] public section

namespace LocalConjugacy.QuaternionExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

instance (priority := high) : TopologicalSpace G := ⊥
instance : DiscreteTopology G := ⟨rfl⟩

/-- The quaternion kernel in its semidirect product. -/
def kernel : Subgroup G := (SemidirectProduct.rightHom : G →* S).ker
instance : kernel.Normal := inferInstanceAs (MonoidHom.ker _).Normal
instance : DecidablePred (· ∈ kernel) := fun g => inferInstanceAs (Decidable (g.right = 1))

/-- The graphs of the trivial cocycle and the central sign cocycle. -/
def complement (b : Bool) : Subgroup G where
  carrier := {g | g.left = if b then signCocycle g.right else 1}
  one_mem' := by cases b <;> decide
  mul_mem' := by cases b <;> decide
  inv_mem' := by cases b <;> decide

instance (b : Bool) : DecidablePred (· ∈ complement b) := fun g =>
  inferInstanceAs (Decidable (g.left = if b then signCocycle g.right else 1))

def two (b : Bool) : Subgroup G where
  carrier := {g | g ∈ complement b ∧ (g.right = 1 ∨ g.right = .sr 0)}
  one_mem' := by cases b <;> decide
  mul_mem' := by cases b <;> decide
  inv_mem' := by cases b <;> decide
instance (b : Bool) : DecidablePred (· ∈ two b) := fun g =>
  inferInstanceAs (Decidable (g ∈ complement b ∧ (g.right = 1 ∨ g.right = .sr 0)))

def three : Subgroup G where
  carrier := {g | g.left = 1 ∧ ∃ i, g.right = DihedralGroup.r i}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide
instance : DecidablePred (· ∈ three) := fun g =>
  inferInstanceAs (Decidable (g.left = 1 ∧ ∃ i, g.right = DihedralGroup.r i))

theorem card_complement : ∀ b, Fintype.card (complement b) = 6 := by decide
theorem card_two : ∀ b, Fintype.card (two b) = 2 := by decide
theorem card_three : Fintype.card three = 3 := by decide

theorem split_complement (b : Bool) : Splits kernel (complement b) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · unfold Supplements
    cases b <;> exact (by decide)
  · ext g
    change (g ∈ kernel ∧ g ∈ complement b) ↔ g = 1
    exact (by decide : ∀ b g, (g ∈ kernel ∧ g ∈ complement b) ↔ g = 1) b g

theorem sylow_two (b : Bool) : IsSylowPro 2 (complement b) (two b) := by
  have hle : two b ≤ complement b := fun _ h => h.1
  apply isSylowPro_of_index _ _ hle
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_two]
  · have h := (two b |>.subgroupOf (complement b)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_two, card_complement] at h
    have : (two b |>.subgroupOf (complement b)).index = 3 := by omega
    rw [this]; decide

theorem sylow_three (b : Bool) : IsSylowPro 3 (complement b) three := by
  have hle : three ≤ complement b := by
    exact (by decide : ∀ b g, g ∈ three → g ∈ complement b) b
  apply isSylowPro_of_index _ _ hle
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_three]
  · have h := (three.subgroupOf (complement b)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_three, card_complement] at h
    have : (three.subgroupOf (complement b)).index = 2 := by omega
    rw [this]; decide

theorem two_conjugate : Conjugate (two false) (two true) := by
  obtain ⟨g, hg⟩ := (by decide : ∃ g : G, ∀ x : G,
    (∃ y : G, y ∈ two false ∧ g * y * g⁻¹ = x) ↔ x ∈ two true)
  refine ⟨g, ?_⟩
  ext x
  exact hg x

theorem complements_locally_conjugate : LocallyConjugate (complement false) (complement true) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst p
    exact ⟨two false, two true, sylow_two false, sylow_two true, two_conjugate⟩
  by_cases h3 : p = 3
  · subst p
    exact ⟨three, three, sylow_three false, sylow_three true, 1, conjugate_one three⟩
  have hs (b : Bool) : IsSylowPro p (complement b) ⊥ := by
    apply isSylowPro_of_index _ _ bot_le IsPGroup.of_bot
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Nat.card_eq_fintype_card, card_complement]
    intro h
    rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from h) with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  exact ⟨⊥, ⊥, hs false, hs true, 1, conjugate_one ⊥⟩

theorem complements_not_conjugate : ¬ Conjugate (complement false) (complement true) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx, hn⟩ := (by decide : ∀ g : G, ∃ x : G,
    x ∈ complement false ∧ g * x * g⁻¹ ∉ complement true) g
  apply hn
  rw [← hg]
  exact Subgroup.mem_map_of_mem _ hx

theorem complement_false_eq_range : complement false =
    (SemidirectProduct.inr : S →* G).range := by
  ext g
  constructor
  · intro hg
    refine ⟨g.right, ?_⟩
    apply SemidirectProduct.ext
    · exact hg.symm
    · rfl
  · rintro ⟨s, rfl⟩
    rfl

/-- The representative classification gives the literal cardinality of H¹. -/
theorem card_H1 : Nat.card (FiniteH1 action) = 2 := by
  let c0 : FiniteCocycle action := ⟨fun _ => 1, exactly_two_classes.1⟩
  let c1 : FiniteCocycle action := ⟨signCocycle, sign_isCocycle⟩
  let f : Bool → FiniteH1 action := fun b =>
    Quotient.mk (finiteCohomologySetoid action) (if b then c1 else c0)
  have hne : f false ≠ f true := by
    intro h
    exact not_equivalent (Quotient.exact h)
  have hi : Function.Injective f := by
    intro b c h
    cases b <;> cases c
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  have hs : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h c =>
      rcases exactly_two_classes.2.2.2 c.val c.property with h | h
      · exact ⟨false, (Quotient.sound h).symm⟩
      · exact ⟨true, (Quotient.sound h).symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Nat.card_eq_fintype_card]
  decide

end LocalConjugacy.QuaternionExample
