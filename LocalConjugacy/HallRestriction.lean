module

public import LocalConjugacy.SupersolvableHallAction

@[expose] public section

/-!
Proposition 2.3 (`prop:res_pi`) of the current manuscript. The Hall subgroup
`Q` is arbitrary, not just the complement chosen in a structural existence
theorem. The proof follows the paper: construct the normal high-prime factor
`M`, show that it centralizes `N`, and extend by `φ(mq) = φ(q)`.
-/

namespace LocalConjugacy

/-- Complementary Hall subgroups, one normal, give the required profinite split. -/
theorem cutoff_hall_isComplement
    {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    {p : ℕ} (M Q : Subgroup J) [M.Normal]
    (hM : IsHallPro {r | p < r} M) (hQ : IsHallPro {r | r ≤ p} Q) :
    M.IsComplement' Q := by
  have hd : Disjoint M Q := by
    apply disjoint_iff_inf_le.mpr
    apply subgroup_le_of_finite_images (M ⊓ Q) ⊥
      (isClosed_singleton : IsClosed ({1} : Set J))
    intro U
    rw [Subgroup.map_bot]
    exact (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)).trans
      (disjoint_of_cutoff_primes (hM.2 U).1 (hQ.2 U).1).le_bot
  have hclosed : IsClosed ((M ⊔ Q : Subgroup J) : Set J) := by
    rw [Subgroup.normal_mul]
    exact hQ.1.mul_left_of_isCompact hM.1.isCompact
  have hsup : M ⊔ Q = ⊤ := by
    apply top_unique
    apply subgroup_le_of_finite_images ⊤ (M ⊔ Q) hclosed
    intro U
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup),
      Subgroup.map_sup]
    apply le_of_eq
    symm
    apply Subgroup.index_eq_one.mp
    by_contra hn
    obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd hn
    have hm := (hM.2 U).2 r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
    have hq := (hQ.2 U).2 r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_right))
    exact hq (Nat.le_of_not_gt hm)
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [← Subgroup.normal_mul, hsup]
  rfl

section Numbered
variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]

/-- Proposition 2.3: restriction is bijective onto all of `H¹(Q,N)`.
The coefficient group is the finite p-group N of arXiv v1. -/
theorem proposition_2_3 [Profinite J] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N]
    (p : ℕ) (hp : p.Prime) (hN : IsPGroup p N)
    (hG : Prosupersolvable (ActionProduct J N))
    (Q : Subgroup J) (hQ : IsHallPro {r | r ≤ p} Q) :
    Function.Bijective (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hJs := prosupersolvable_acting_group hG
  let M := upperHall hJs p
  have hM := upperHall_isHallPro hJs p
  have hMQ := cutoff_hall_isComplement M Q hM hQ
  have hact := prosupersolvable_action_trivial_on_high_primes hG hN M hM.hasProPrimes
  have hres := hall_complement_restriction hN M Q hM.1 hQ.1 hMQ hM.hasProPrimes hact
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        exact Quotient.sound (hres.1 f g (Quotient.exact hab))
  · intro b
    induction b using Quotient.inductionOn with
    | h φ =>
      obtain ⟨φ', hφ'⟩ := extend_cocycle_across_trivial_factor M Q hM.1 hQ.1 hMQ hact φ
      refine ⟨Quotient.mk _ φ', ?_⟩
      change Quotient.mk _ (restrictCocycle le_top φ') = Quotient.mk _ φ
      rw [hφ']

end Numbered
end LocalConjugacy
