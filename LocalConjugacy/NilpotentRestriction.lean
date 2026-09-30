module

public import LocalConjugacy.RestrictionComposition

@[expose] public section

namespace LocalConjugacy

/-- Maximal subgroups of a finite nilpotent group have prime index. This is
the finite induction step used in the nilpotent case of Lemma 1.2. -/
theorem nilpotent_coatom_prime_index {J : Type*} [Group J] [Finite J]
    [Group.IsNilpotent J] (K : Subgroup J) (hK : IsCoatom K) :
    K.Normal ∧ K.index.Prime := by
  have hn : K.Normal := (Group.isNilpotent_of_finite_tfae.out 1 3 rfl rfl).mp
    inferInstance K hK
  letI := hn
  letI : Nontrivial (J ⧸ K) := QuotientGroup.nontrivial_iff.mpr hK.1
  let π := QuotientGroup.mk' K
  letI : IsSimpleGroup (J ⧸ K) :=
    { eq_bot_or_eq_top_of_normal := fun D _ => by
        have hle : K ≤ D.comap π := by
          simpa only [π, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap π D
        rcases eq_or_lt_of_le hle with he | he
        · left
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          change D.comap π = π.ker
          simpa only [π, QuotientGroup.ker_mk'] using he.symm
        · right
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          rw [Subgroup.comap_top]
          exact hK.2 _ he }
  exact ⟨hn, IsSimpleGroup.prime_card (α := J ⧸ K)⟩

theorem subgroup_card_lt_of_ne_top {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) (hK : K ≠ ⊤) : Nat.card K < Nat.card J := by
  exact lt_of_le_of_ne (Nat.card_le_card_of_injective K.subtype Subtype.val_injective)
    (fun he => hK (K.eq_top_of_card_eq he))

universe u v

private theorem finite_nilpotent_sylow_restriction_aux
    {N : Type v} [Group N] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N) (n : ℕ) :
    ∀ {J : Type u} [Group J] [TopologicalSpace J] [DiscreteTopology J] [Finite J]
      [Group.IsNilpotent J] [MulDistribMulAction J N],
      Nat.card J = n → ∀ P : Sylow p J,
      RestrictionIsomorphism (N := N) ⊤ P.toSubgroup le_top := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ _ _ _ _ hcard P
    letI : Profinite J := ⟨⟩
    letI : ContinuousSMul J N := ⟨continuous_of_discreteTopology⟩
    rcases eq_top_or_exists_le_coatom P.toSubgroup with hP | ⟨K, hK, hPK⟩
    · rw [hP]
      exact restrictionIsomorphism_refl ⊤
    · obtain ⟨hn, hprime⟩ := nilpotent_coatom_prime_index K hK
      letI := hn
      letI : Fact K.index.Prime := ⟨hprime⟩
      have hne : K.index ≠ p := by
        intro he
        have hd : K.index ∣ P.toSubgroup.index := Subgroup.index_dvd_of_le hPK
        rw [he] at hd
        exact P.not_dvd_index hd
      have hi := ih (Nat.card K) (hcard ▸ subgroup_card_lt_of_ne_top K hK.1)
        (J := K) rfl (P.subtype hPK)
      have hi' : RestrictionIsomorphism (N := N) K P.toSubgroup hPK :=
        restrictionIsomorphism_of_subgroup hPK hi
      exact restrictionIsomorphism_comp K P.toSubgroup hPK
        (coprime_prime_index_restriction (p := p) (q := K.index) hne hN K (isClosed_discrete _) rfl) hi'

/-- The primary restriction isomorphism for finite nilpotent acting groups
and finite `p`-group coefficients, with no commutativity of the coefficients. -/
theorem finite_nilpotent_sylow_restriction
    {J : Type u} {N : Type v} [Group J] [Group N]
    [TopologicalSpace J] [DiscreteTopology J] [Finite J] [Group.IsNilpotent J]
    [TopologicalSpace N] [DiscreteTopology N] [Finite N]
    [MulDistribMulAction J N] {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Sylow p J) :
    RestrictionIsomorphism (N := N) ⊤ P.toSubgroup le_top :=
  finite_nilpotent_sylow_restriction_aux hN (Nat.card J) rfl P

end LocalConjugacy
