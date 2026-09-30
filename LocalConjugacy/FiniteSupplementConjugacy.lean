module

public import LocalConjugacy.PGroupSupplementReduction
public import LocalConjugacy.SupplementInductionTools
public import LocalConjugacy.NilpotentCoprimeFactors

@[expose] public section

namespace LocalConjugacy

universe u

/-- The finite induction follows Proposition 3.2: split coprime normal
factors, then align a Sylow and pass to the generated subgroup or a quotient. -/
private theorem finite_supplement_conjugacy_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
      (N H K : Subgroup G) [N.Normal] [Group.IsNilpotent N],
      Nat.card N = n →
      (Supersolvable G ∨ Group.IsNilpotent (G ⧸ N)) →
      Supplements N H → Supplements N K → LocallyConjugate H K → Conjugate H K := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ _ N H K _ _ hcard hcase hsH hsK hlocal
    letI : Profinite G := ⟨⟩
    have hquot (X Y D : Subgroup G) [D.Normal] (hDN : D ≤ N) (hD : D ≠ ⊥)
        (hsX : Supplements N X) (hsY : Supplements N Y) (hl : LocallyConjugate X Y) :
        Conjugate (X.map (QuotientGroup.mk' D)) (Y.map (QuotientGroup.mk' D)) := by
      let π := QuotientGroup.mk' D
      letI := nilpotent_subgroup_map N π
      exact ih _ (hcard ▸ card_map_quotient_lt N D hDN hD)
        (N.map π) (X.map π) (Y.map π) rfl
        (conjugacy_case_map N π (QuotientGroup.mk'_surjective D) hcase)
        (supplements_map N X hsX π (QuotientGroup.mk'_surjective D))
        (supplements_map N Y hsY π (QuotientGroup.mk'_surjective D))
        (locallyConjugate_map_finite X Y (isClosed_discrete _) (isClosed_discrete _)
          hl π continuous_quotient_mk')
    by_cases hpgroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p N
    · obtain ⟨p, hp, hNp⟩ := hpgroup
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨P, Q, hP, hQ, g, hg⟩ := hlocal p hp
      let H' := conjugate g H
      have hsH' : Supplements N H' := supplements_conjugate N H hsH g
      have hlocal' : LocallyConjugate H' K := hlocal.conjugate_left g
      have hQH : IsSylowPro p H' Q := by
        rw [← hg]
        exact isSylowPro_conjugate g H P hP
      apply Conjugate.trans (show Conjugate H H' from ⟨g, rfl⟩)
      by_cases hgen : H' ⊔ K = ⊤
      · obtain ⟨he, hn⟩ := normal_inf_of_common_sylow N H' K Q hNp hQH hQ hgen
        let D := N ⊓ H'
        letI : D.Normal := hn
        by_cases hD : D = ⊥
        · have hpro : Prosupersolvable G ∨ Pronilpotent (G ⧸ N) := by
            rcases hcase with h | h
            · exact Or.inl (prosupersolvable_iff_supersolvable.mpr h)
            · exact Or.inr (pronilpotent_iff_nilpotent.mpr h)
          exact (finite_complement_conjugacy N H' K (isClosed_discrete _) (isClosed_discrete _)
            (isClosed_discrete _) (pronilpotent_iff_nilpotent.mpr inferInstance) hpro
            hsH' hsK hD (he ▸ hD)).mpr hlocal'
        · have hDK : D ≤ K := by rw [show D = N ⊓ K from he]; exact inf_le_right
          exact conjugate_of_map_eq D H' K inf_le_right hDK
            (hquot H' K D inf_le_left hD hsH' hsK hlocal')
      · let L := H' ⊔ K
        have hNL : ¬ N ≤ L := by
          intro hle
          apply hgen
          apply top_unique
          rw [← sup_eq_top_of_supplements N H' hsH']
          exact sup_le hle le_sup_left
        letI := nilpotent_subgroupOf N L
        have hl := locallyConjugate_generated_of_common_sylow N H' K Q hNp hsH' hsK hQH hQ
        have hc := ih _ (hcard ▸ card_subgroupOf_lt_of_not_le N L hNL)
          (N.subgroupOf L) (H'.subgroupOf L) (K.subgroupOf L) rfl
          (conjugacy_case_subgroup N L hcase)
          (supplements_subgroupOf N H' L hsH' le_sup_left)
          (supplements_subgroupOf N K L hsK le_sup_right) hl
        have hm := hc.map L.subtype
        simpa only [Subgroup.map_subgroupOf_eq_of_le (show H' ≤ L from le_sup_left),
          Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_right)] using hm
    · obtain ⟨A₀, B₀, hAc, hBc, hc, hcop, hA₀, hB₀⟩ := nilpotent_coprime_split hpgroup
      letI := hAc
      letI := hBc
      let A := A₀.map N.subtype
      let B := B₀.map N.subtype
      letI : A.Normal := inferInstance
      letI : B.Normal := inferInstance
      have hAN : A ≤ N := by
        simpa only [N.range_subtype] using A₀.map_le_range N.subtype
      have hBN : B ≤ N := by
        simpa only [N.range_subtype] using B₀.map_le_range N.subtype
      have hAB : A ⊔ B = N := by
        change A₀.map N.subtype ⊔ B₀.map N.subtype = N
        rw [← Subgroup.map_sup, hc.sup_eq_top, ← MonoidHom.range_eq_map, N.range_subtype]
      have hA : A ≠ ⊥ := by
        intro h
        apply hA₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hB : B ≠ ⊥ := by
        intro h
        apply hB₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hcop' : (Nat.card A).Coprime (Nat.card B) := by
        simpa only [A, B, Subgroup.card_map_of_injective N.subtype_injective] using hcop
      have hd : Disjoint A B := Subgroup.disjoint_of_coprime_natCard hcop'
      have hqA := hquot H K A hAN hA hsH hsK hlocal
      have hqB := hquot H K B hBN hB hsH hsK hlocal
      have inclusion (X Y : Subgroup G) (hsX : Supplements N X)
          (hAq : Conjugate (X.map (QuotientGroup.mk' A)) (Y.map (QuotientGroup.mk' A)))
          (hBq : Conjugate (X.map (QuotientGroup.mk' B)) (Y.map (QuotientGroup.mk' B))) :
          ∃ g : G, conjugate g X ≤ Y := by
        obtain ⟨b, hb⟩ := quotient_conjugator_from_factor A B N X Y hsX hAB hAq
        obtain ⟨a, ha⟩ := quotient_conjugator_from_factor B A N X Y hsX
          ((sup_comm B A).trans hAB) hBq
        exact ⟨(a : G) * b, merge_coprime_conjugators A B X Y hcop' hd a b
          (conjugate_le_sup_of_quotient A X Y b hb.le)
          (conjugate_le_sup_of_quotient B X Y a ha.le)⟩
      exact conjugate_of_mutual_inclusions H K (inclusion H K hsH hqA hqB)
        (inclusion K H hsK hqA.symm hqB.symm)

/-- Proposition 3.2's finite induction, with the ambient group finite.
The unrestricted profinite statement is obtained by finite quotients. -/
theorem finite_nilpotent_supplement_conjugacy
    {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (N H K : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hcase : Supersolvable G ∨ Group.IsNilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  letI : Profinite G := ⟨⟩
  exact ⟨locallyConjugate_of_conjugate H K (isClosed_discrete _),
    finite_supplement_conjugacy_aux (Nat.card N) N H K rfl hcase hHN hKN⟩

end LocalConjugacy
