module

public import LocalConjugacy.FiniteSylow
public import LocalConjugacy.Actions

@[expose] public section

/-!
The imprimitive wreath product `C₃ wr S₃`, of order 162, acting on nine
points. Its normal Heisenberg subgroup is the kernel of the base-sum/sign
map to `C₃ × C₂`. The chosen cyclic complement translates block zero and
interchanges the other two blocks. Its Sylow subgroups have disjoint fixed
point sets. This is the second example in the manuscript.
-/

namespace LocalConjugacy.HeisenbergExample

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev B := ZMod 3 → C3
abbrev S := DihedralGroup 3

def perm : S → ZMod 3 → ZMod 3
  | .r a, i => a + i
  | .sr a, i => -(a + i)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem perm_one : ∀ i, perm 1 i = i := by decide
theorem perm_mul : ∀ s t i, perm (s * t) i = perm s (perm t i) := by decide

def action : S →* MulAut B where
  toFun s :=
    { toFun := fun b i => b (perm s⁻¹ i)
      invFun := fun b i => b (perm s i)
      left_inv := fun b => by ext i; dsimp; rw [← perm_mul, inv_mul_cancel, perm_one]
      right_inv := fun b => by ext i; dsimp; rw [← perm_mul, mul_inv_cancel, perm_one]
      map_mul' := fun _ _ => rfl }
  map_one' := by ext b i; dsimp; rw [inv_one, perm_one]
  map_mul' s t := by ext b i; dsimp; rw [mul_inv_rev, perm_mul]

abbrev G := B ⋊[action] S
instance : Fintype G := Fintype.ofEquiv (B × S) SemidirectProduct.equivProd.symm
instance (priority := high) : DecidableEq G := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
     fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩
instance (priority := high) : TopologicalSpace G := ⊥
instance : DiscreteTopology G := ⟨rfl⟩

def sign : S →* C2 where
  toFun s := match s with | .r _ => 1 | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by decide

def sumBase : B →* C3 where
  toFun b := b 0 * b 1 * b 2
  map_one' := rfl
  map_mul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc]

def baseMap : B →* C3 × C2 := sumBase.prod 1
def permMap : S →* C3 × C2 := (1 : S →* C3).prod sign

theorem compatibility : ∀ s : S,
    baseMap.comp (action s).toMonoidHom =
      (MulAut.conj (permMap s)).toMonoidHom.comp baseMap := by
  intro s
  apply MonoidHom.ext
  exact (by decide : ∀ s : S, ∀ b : B,
    baseMap (action s b) = permMap s * baseMap b * (permMap s)⁻¹) s

/-- Quotient by the normal Heisenberg subgroup. -/
def projection : G →* C3 × C2 := SemidirectProduct.lift baseMap permMap compatibility

/-- Kernel: base vectors of sum zero, with even block permutation. -/
def N : Subgroup G := projection.ker
instance : DecidablePred (· ∈ N) := fun _ => inferInstanceAs (Decidable (projection _ = 1))
instance : N.Normal := inferInstanceAs projection.ker.Normal

/-- A section of the quotient: change only block zero and optionally swap
blocks one and two. Thus its image is a cyclic complement of order six. -/
def sectionMap : C3 × C2 →* G where
  toFun z := ⟨fun i => if i = 0 then z.1 else 1,
    if z.2 = 1 then 1 else DihedralGroup.sr 0⟩
  map_one' := by decide
  map_mul' := by decide

theorem projection_section : ∀ z : C3 × C2, projection (sectionMap z) = z := by decide

def J : Subgroup G := sectionMap.range
instance : DecidablePred (· ∈ J) := fun _ =>
  inferInstanceAs (Decidable (∃ z : C3 × C2, sectionMap z = _))

theorem split : Splits N J := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro g
    refine ⟨g * (sectionMap (projection g))⁻¹, ?_, sectionMap (projection g), ?_, ?_⟩
    · change projection (g * (sectionMap (projection g))⁻¹) = 1
      rw [map_mul, map_inv, projection_section]
      exact mul_inv_cancel (projection g)
    · exact ⟨projection g, rfl⟩
    · simp
  · apply le_antisymm _ bot_le
    intro g hg
    obtain ⟨z, rfl⟩ := hg.2
    have hz : z = 1 := (projection_section z).symm.trans hg.1
    simp [hz]

theorem card_N : Fintype.card N = 27 := by decide
theorem card_J : Fintype.card J = 6 := by decide
theorem nilpotent_N : Group.IsNilpotent N := by
  apply (IsPGroup.of_card (p := 3) (n := 3) ?_).isNilpotent
  simpa [Nat.card_eq_fintype_card] using card_N

abbrev Ω := ZMod 3 × C3

def move (g : G) (x : Ω) : Ω :=
  (perm g.right x.1, g.left (perm g.right x.1) * x.2)

instance : MulAction G Ω where
  smul := move
  one_smul := by decide
  mul_smul g h x := by
    apply Prod.ext
    · exact perm_mul _ _ _
    · change g.left (perm (g.right * h.right) x.1) *
        h.left (perm g.right⁻¹ (perm (g.right * h.right) x.1)) * x.2 =
        g.left (perm g.right (perm h.right x.1)) * (h.left (perm h.right x.1) * x.2)
      rw [perm_mul, ← perm_mul g.right⁻¹ g.right, inv_mul_cancel, perm_one, mul_assoc]

def H : Subgroup G := MulAction.stabilizer G ((0, 1) : Ω)
instance : DecidablePred (· ∈ H) := fun g => inferInstanceAs (Decidable (move g (0, 1) = (0, 1)))

theorem card_H : Fintype.card H = 18 := by decide

/-- Elements generating the Sylow 3- and Sylow 2-subgroups of the complement. -/
def c : G := sectionMap (Multiplicative.ofAdd 1, 1)
def t : G := sectionMap (1, Multiplicative.ofAdd 1)
def shift : G := ⟨1, .r 1⟩

theorem order_c : orderOf c = 3 := by
  apply orderOf_eq_prime
  · decide
  · decide

theorem order_t : orderOf t = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

theorem c_fixed : ∃ x : Ω, c • x = x := by decide
theorem t_fixed : ∃ x : Ω, t • x = x := by decide
theorem no_common_fixed : ¬ ∃ x : Ω, c • x = x ∧ t • x = x := by decide

theorem no_J_fixed : ¬ HasFixedPoint (Ω := Ω) J := by
  rintro ⟨x, hx⟩
  apply no_common_fixed
  exact ⟨x, hx c ⟨_, rfl⟩, hx t ⟨_, rfl⟩⟩

theorem transitive_N : ∀ x y : Ω, ∃ n : N, (n : G) • x = y := by decide

theorem intersection_not_normal : ¬ IntersectionNormal N H := by
  change ¬ ∀ n : G, n ∈ N → ∀ d : G, (d ∈ N ∧ d ∈ H) →
    (n * d * n⁻¹ ∈ N ∧ n * d * n⁻¹ ∈ H)
  decide

/-- A small finite certificate for the failure of local inclusion. -/
theorem inclusion_obstruction :
    (∃ g : G, g * c * g⁻¹ ∈ H) ∧ t ∈ H ∧
      (∀ g : G, ¬ (g * c * g⁻¹ ∈ H ∧ g * t * g⁻¹ ∈ H)) := by decide

def P3 : Subgroup G := (sectionMap.comp (MonoidHom.inl C3 C2)).range
def P2 : Subgroup G := (sectionMap.comp (MonoidHom.inr C3 C2)).range
instance : DecidablePred (· ∈ P3) := fun x =>
  inferInstanceAs (Decidable (∃ z : C3, sectionMap (z, 1) = x))
instance : DecidablePred (· ∈ P2) := fun x =>
  inferInstanceAs (Decidable (∃ z : C2, sectionMap (1, z) = x))

theorem P3_le : P3 ≤ J := by rintro x ⟨z, rfl⟩; exact ⟨(z, 1), rfl⟩
theorem P2_le : P2 ≤ J := by rintro x ⟨z, rfl⟩; exact ⟨(1, z), rfl⟩
theorem card_P3 : Fintype.card P3 = 3 := by decide
theorem card_P2 : Fintype.card P2 = 2 := by decide

theorem index_P3 : (P3.subgroupOf J).index = 2 := by
  have h := (P3.subgroupOf J).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_P3, card_J] at h
  omega

theorem index_P2 : (P2.subgroupOf J).index = 3 := by
  have h := (P2.subgroupOf J).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P2_le).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_P2, card_J] at h
  omega

theorem sylow_P3 : IsSylowPro 3 J P3 := by
  apply isSylowPro_of_index J P3 P3_le
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_P3]
  · rw [index_P3]; decide

theorem sylow_P2 : IsSylowPro 2 J P2 := by
  apply isSylowPro_of_index J P2 P2_le
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_P2]
  · rw [index_P2]; decide

theorem locally_contains : LocallyContains H J := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    refine ⟨P2, sylow_P2, 1, ?_⟩
    rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    exact (by decide : ∀ z : C2, (1 : G) * sectionMap (1, z) * 1⁻¹ ∈ H) z
  by_cases hp3 : p = 3
  · subst p
    refine ⟨P3, sylow_P3, shift, ?_⟩
    rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    exact (by decide : ∀ z : C3, shift * sectionMap (z, 1) * shift⁻¹ ∈ H) z
  refine ⟨⊥, isSylowPro_of_index J ⊥ bot_le (IsPGroup.of_bot) ?_, 1, ?_⟩
  · rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Nat.card_eq_fintype_card, card_J]
    intro h
    have h' : p ∣ 2 * 3 := h
    rcases hp.dvd_mul.mp h' with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3)
  · simp [conjugate]

theorem not_contains : ¬ ∃ g : G, conjugate g J ≤ H := by
  rintro ⟨g, hg⟩
  exact no_J_fixed (fixedPoint_of_conjugate_le_stabilizer J ((0, 1) : Ω) g hg)

theorem cyclic_J : IsCyclic J := by
  let z : J := ⟨c * t, J.mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩⟩
  apply isCyclic_of_orderOf_eq_card z
  rw [Nat.card_eq_fintype_card, card_J]
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · apply Subtype.ext; decide
  · intro m hm hm0
    interval_cases m <;> decide

theorem pronilpotent_N : Pronilpotent N := by
  let := nilpotent_N
  intro U
  infer_instance

theorem pronilpotent_J : Pronilpotent J := by
  let := cyclic_J
  let : CommGroup J := IsCyclic.commGroup
  intro U
  infer_instance

theorem exponent_three_N : ∀ n : N, n ^ 3 = 1 := by decide
theorem nonabelian_N : ¬ ∀ n m : N, n * m = m * n := by decide

/-- Failure of Corollary 1.3 when normality of `N ∩ H` in `N` is removed. -/
theorem counterexample :
    Profinite G ∧ Splits N J ∧ Pronilpotent N ∧ Pronilpotent J ∧
    IsClosed (N : Set G) ∧ IsClosed (J : Set G) ∧ IsClosed (H : Set G) ∧
    LocallyContains H J ∧ (¬ ∃ g : G, conjugate g J ≤ H) ∧
    ¬ IntersectionNormal N H := by
  exact ⟨⟨⟩,
    split, pronilpotent_N, pronilpotent_J, isClosed_discrete _, isClosed_discrete _,
    isClosed_discrete _, locally_contains, not_contains, intersection_not_normal⟩

end LocalConjugacy.HeisenbergExample
