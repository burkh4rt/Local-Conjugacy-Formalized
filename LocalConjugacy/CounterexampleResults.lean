module

public import LocalConjugacy.Counterexamples.QuaternionSylow
public import LocalConjugacy.Counterexamples.HeisenbergSupersolvable
public import LocalConjugacy.Counterexamples.HeisenbergIdentification

@[expose] public section

namespace LocalConjugacy

set_option maxRecDepth 10000

/-- The Introduction's Q₈ ⋊ S₃ counterexample inside GL(2,3): exactly two
classes in H¹(S₃,Q₈), trivial H¹ on every Sylow subgroup, and two actual
complements that are locally conjugate but not conjugate in the ambient group. -/
theorem counterexample_quaternion :
    ∃ a : DihedralGroup 3 →* MulAut (QuaternionGroup 2),
    Nonempty ((QuaternionGroup 2 ⋊[a] DihedralGroup 3) ≃* GL (Fin 2) (ZMod 3)) ∧
    Nat.card (FiniteH1 a) = 2 ∧
    (∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ P : Sylow p (DihedralGroup 3),
        Subsingleton (FiniteH1 (a.comp P.toSubgroup.subtype))) ∧
    (let G := QuaternionGroup 2 ⋊[a] DihedralGroup 3
     letI : TopologicalSpace G := ⊥
     let N := (SemidirectProduct.rightHom : G →* DihedralGroup 3).ker
     let J := (SemidirectProduct.inr : DihedralGroup 3 →* G).range
     ∃ J' : Subgroup G, Splits N J ∧ Splits N J' ∧
       LocallyConjugate J J' ∧ ¬ Conjugate J J') := by
  refine ⟨QuaternionExample.action, ⟨QuaternionExample.equivGL⟩,
    QuaternionExample.card_H1, ?_, ?_⟩
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    exact QuaternionExample.sylow_H1_subsingleton p
  · change ∃ J', Splits QuaternionExample.kernel _ ∧ Splits QuaternionExample.kernel J' ∧ _
    rw [← QuaternionExample.complement_false_eq_range]
    exact ⟨QuaternionExample.complement true, QuaternionExample.split_complement false,
      QuaternionExample.split_complement true, QuaternionExample.complements_locally_conjugate,
      QuaternionExample.complements_not_conjugate⟩

/-- The order-162 counterexample to local inclusion without the normality
of `N ∩ H` in `N`. In the construction, `G = C₃ wr S₃`, `|N| = 27`,
`J` is cyclic of order 6, and `H ≃ C₃ × S₃` has order 18. -/
theorem counterexample_heisenberg :
    ∃ (G : ProfiniteGrp.{0}) (N J H : Subgroup G),
    Finite G ∧ Nonempty (G ≃* WreathC3S3) ∧ Nonempty (N ≃* Heisenberg3) ∧
    Nonempty (J ≃* Multiplicative (ZMod 6)) ∧
    Group.IsNilpotent N ∧ Group.IsNilpotent J ∧ Nat.card G = 162 ∧ Nat.card N = 27 ∧ Nat.card J = 6 ∧ Nat.card H = 18 ∧
    Nonempty (H ≃* Multiplicative (ZMod 3) × DihedralGroup 3) ∧
    Splits N J ∧ Pronilpotent N ∧ Pronilpotent J ∧ Supersolvable G ∧ IsCyclic J ∧
    (∀ n : N, n ^ 3 = 1) ∧ (¬ ∀ n m : N, n * m = m * n) ∧
    IsClosed (N : Set G) ∧ IsClosed (J : Set G) ∧ IsClosed (H : Set G) ∧
    LocallyContains H J ∧ (¬ ∃ g : G, conjugate g J ≤ H) ∧
    ¬ IntersectionNormal N H := by
  refine ⟨ProfiniteGrp.of HeisenbergExample.G, HeisenbergExample.N,
    HeisenbergExample.J, HeisenbergExample.H, inferInstance,
    ⟨HeisenbergExample.gEquivWreath⟩, ⟨HeisenbergExample.nEquivHeisenberg⟩,
    ⟨HeisenbergExample.jEquivC6⟩, HeisenbergExample.nilpotent_N, ?_, ?_, ?_, ?_, ?_,
    ⟨HeisenbergExample.hEquivProduct⟩,
    HeisenbergExample.split, HeisenbergExample.pronilpotent_N,
    HeisenbergExample.pronilpotent_J, HeisenbergExample.supersolvable_G, HeisenbergExample.cyclic_J,
    HeisenbergExample.exponent_three_N, HeisenbergExample.nonabelian_N,
    isClosed_discrete _, isClosed_discrete _, isClosed_discrete _,
    HeisenbergExample.locally_contains, HeisenbergExample.not_contains,
    HeisenbergExample.intersection_not_normal⟩
  · letI := HeisenbergExample.cyclic_J
    letI : CommGroup HeisenbergExample.J := IsCyclic.commGroup
    infer_instance
  · rw [Nat.card_eq_fintype_card]; decide
  · simpa [Nat.card_eq_fintype_card] using HeisenbergExample.card_N
  · simpa [Nat.card_eq_fintype_card] using HeisenbergExample.card_J
  · simpa [Nat.card_eq_fintype_card] using HeisenbergExample.card_H

end LocalConjugacy
