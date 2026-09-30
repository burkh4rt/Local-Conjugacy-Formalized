module

public import LocalConjugacy.NilpotentCoefficients
public import LocalConjugacy.FiniteHall

@[expose] public section

namespace LocalConjugacy
open NilpotentCoefficients

section Factors
variable {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]

theorem nilpotent_primary_complement (p : PrimeIndex G) :
    ∃ B : Subgroup G, B.Characteristic ∧ (Factor G p).IsComplement' B ∧
      (Nat.card (Factor G p)).Coprime (Nat.card B) := by
  classical
  letI (q : PrimeIndex G) := Fintype.ofFinite (Factor G q)
  let B : Subgroup G := ⨆ q : {q : PrimeIndex G // q ≠ p}, Factor G q.val
  have hi : iSupIndep (Factor G) := by
    apply Subgroup.independent_of_coprime_order factors_commute
    intro q r hqr
    simpa only [Nat.card_eq_fintype_card] using IsPGroup.coprime_card_of_ne q.val r.val
      (fun he => hqr (Subtype.ext he)) _ _ (primarySylow q).isPGroup' (primarySylow r).isPGroup'
  have hd : Disjoint (Factor G p) B := by
    exact (hi p).mono_right (iSup_le fun q => le_iSup_of_le q.val
      (le_iSup (fun _ : q.val ≠ p => Factor G q.val) q.property))
  have hs : Factor G p ⊔ B = ⊤ := by
    have hr : (⨆ q : PrimeIndex G, Factor G q) = ⊤ := by
      rw [← Subgroup.noncommPiCoprod_range (hcomm := factors_commute)]
      exact (Subgroup.noncommPiCoprod factors_commute).range_eq_top_of_surjective
        (productEquiv (N := G)).surjective
    rw [← hr]
    apply le_antisymm
    · exact sup_le (le_iSup (Factor G) p) (iSup_le fun q => le_iSup (Factor G) q.val)
    · apply iSup_le
      intro q
      by_cases he : q = p
      · exact he ▸ le_sup_left
      · exact (le_iSup (fun r : {r : PrimeIndex G // r ≠ p} => Factor G r.val) ⟨q, he⟩).trans le_sup_right
  have hc : (Factor G p).IsComplement' B := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [← Subgroup.normal_mul, hs]
    rfl
  exact ⟨B, inferInstance, hc, hc.card_right ▸ (primarySylow p).card_coprime_index⟩

theorem nilpotent_coprime_split (h : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p G) :
    ∃ A B : Subgroup G, A.Characteristic ∧ B.Characteristic ∧
      A.IsComplement' B ∧ (Nat.card A).Coprime (Nat.card B) ∧ A ≠ ⊥ ∧ B ≠ ⊥ := by
  classical
  have hn : Nat.card G ≠ 1 := by
    intro he
    letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp he).1
    exact h ⟨2, Nat.prime_two, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
  let q : PrimeIndex G := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.card_pos.ne'⟩⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB, hc, hcop⟩ := nilpotent_primary_complement q
  refine ⟨Factor G q, B, inferInstance, hB, hc, hcop,
    (primarySylow q).ne_bot_of_dvd_card hpd, ?_⟩
  intro he
  have htop := hc.sup_eq_top
  rw [he, sup_bot_eq] at htop
  have hpg : IsPGroup p (Factor G q) := (primarySylow q).isPGroup'
  rw [htop] at hpg
  exact h ⟨p, hp, hpg.of_equiv Subgroup.topEquiv⟩

end Factors
end LocalConjugacy
