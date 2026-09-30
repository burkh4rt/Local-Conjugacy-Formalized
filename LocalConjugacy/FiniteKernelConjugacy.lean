module

public import LocalConjugacy.FiniteKernelSylow
public import LocalConjugacy.NilpotentCoprimeFactors

@[expose] public section

/-! Proposition 3.2's induction on the order of the finite normal subgroup.
The ambient group is profinite throughout, as in the current manuscript. -/

namespace LocalConjugacy
universe u

private theorem finite_kernel_conjugacy_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
      (N H K : Subgroup G) [N.Normal] [Finite N] [Group.IsNilpotent N],
      Nat.card N = n → IsClosed (N : Set G) → IsClosed (H : Set G) →
      IsClosed (K : Set G) →
      (Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) →
      Supplements N H → Supplements N K → LocallyConjugate H K → Conjugate H K := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ N H K _ _ _ hcard hN hH hK hcase hsH hsK hlocal
    have hquot (X Y D : Subgroup G) [D.Normal] (hDN : D ≤ N) (hD : D ≠ ⊥)
        (hX : IsClosed (X : Set G)) (hY : IsClosed (Y : Set G))
        (hsX : Supplements N X) (hsY : Supplements N Y) (hl : LocallyConjugate X Y) :
        Conjugate (X.map (QuotientGroup.mk' D)) (Y.map (QuotientGroup.mk' D)) := by
      letI : Finite D := Finite.of_injective (Subgroup.inclusion hDN)
        (Subgroup.inclusion_injective hDN)
      have hDc : IsClosed (D : Set G) :=
        (Set.finite_coe_iff.mp (inferInstance : Finite D)).isClosed
      letI := profinite_quotient D hDc
      let π := QuotientGroup.mk' D
      letI := nilpotent_subgroup_map N π
      letI : Finite (N.map π) := Finite.of_surjective (subgroupImageHom N π)
        (subgroupImageHom_surjective N π)
      exact ih _ (hcard ▸ card_map_quotient_lt_finite_kernel N D hDN hD)
        (N.map π) (X.map π) (Y.map π) rfl
        (hN.isCompact.image continuous_quotient_mk').isClosed
        (hX.isCompact.image continuous_quotient_mk').isClosed
        (hY.isCompact.image continuous_quotient_mk').isClosed
        (profinite_conjugacy_case_map N π continuous_quotient_mk'
          (QuotientGroup.mk'_surjective D) hcase)
        (supplements_map N X hsX π (QuotientGroup.mk'_surjective D))
        (supplements_map N Y hsY π (QuotientGroup.mk'_surjective D))
        (locallyConjugate_map X Y hX hY hl π continuous_quotient_mk')
    by_cases hpgroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p N
    · obtain ⟨p, hp, hNp⟩ := hpgroup
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨P, Q, hP, hQ, g, hg⟩ := hlocal p hp
      let H' := conjugate g H
      have hH' : IsClosed (H' : Set G) := conjugate_closed g H hH
      have hsH' : Supplements N H' := supplements_conjugate N H hsH g
      have hlocal' : LocallyConjugate H' K := hlocal.conjugate_left g
      have hQH : IsSylowPro p H' Q := by
        rw [← hg]
        exact isSylowPro_conjugate g H P hP
      apply Conjugate.trans (show Conjugate H H' from ⟨g, rfl⟩)
      by_cases hgen : H' ⊔ K = ⊤
      · obtain ⟨he, hn⟩ := normal_inf_of_common_sylow_profinite N H' K Q hH' hK hNp hQH hQ hgen
        let D := N ⊓ H'
        letI : D.Normal := hn
        by_cases hD : D = ⊥
        · exact (finite_complement_conjugacy N H' K hN hH' hK
            (pronilpotent_iff_nilpotent.mpr inferInstance) hcase
            hsH' hsK hD (he ▸ hD)).mpr hlocal'
        · have hDK : D ≤ K := by rw [show D = N ⊓ K from he]; exact inf_le_right
          exact conjugate_of_map_eq D H' K inf_le_right hDK
            (hquot H' K D inf_le_left hD hH' hK hsH' hsK hlocal')
      · let L := H' ⊔ K
        letI := finiteIndex_of_finite_supplement N H' hsH'
        have hL : IsClosed (L : Set G) := Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono le_sup_left (H'.isOpen_of_isClosed_of_finiteIndex hH'))
        letI := profinite_closed_subgroup L hL
        have hNL : ¬ N ≤ L := by
          intro hle
          apply hgen
          apply top_unique
          rw [← sup_eq_top_of_supplements N H' hsH']
          exact sup_le hle le_sup_left
        letI := nilpotent_subgroupOf N L
        let f : N.subgroupOf L → N := fun x => ⟨x.val.val, x.property⟩
        letI : Finite (N.subgroupOf L) := Finite.of_injective f (by
          intro x y he
          have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) he
          exact Subtype.ext (Subtype.ext hv))
        have hl := locallyConjugate_generated_profinite N H' K Q hH' hK hL hNp hsH' hsK hQH hQ
        have hc := ih _ (hcard ▸ card_subgroupOf_lt_finite_kernel N L hNL)
          (N.subgroupOf L) (H'.subgroupOf L) (K.subgroupOf L) rfl
          (hN.preimage continuous_subtype_val) (hH'.preimage continuous_subtype_val)
          (hK.preimage continuous_subtype_val) (profinite_conjugacy_case_subgroup N L hN hL hcase)
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
      have hqA := hquot H K A hAN hA hH hK hsH hsK hlocal
      have hqB := hquot H K B hBN hB hH hK hsH hsK hlocal
      have inclusion (X Y : Subgroup G) (hY : IsClosed (Y : Set G)) (hsX : Supplements N X)
          (hAq : Conjugate (X.map (QuotientGroup.mk' A)) (Y.map (QuotientGroup.mk' A)))
          (hBq : Conjugate (X.map (QuotientGroup.mk' B)) (Y.map (QuotientGroup.mk' B))) :
          ∃ g : G, conjugate g X ≤ Y := by
        obtain ⟨b, hb⟩ := quotient_conjugator_from_factor A B N X Y hsX hAB hAq
        obtain ⟨a, ha⟩ := quotient_conjugator_from_factor B A N X Y hsX
          ((sup_comm B A).trans hAB) hBq
        exact ⟨(a : G) * b, merge_coprime_conjugators_profinite A B X Y hY hcop' hd a b
          (conjugate_le_sup_of_quotient A X Y b hb.le)
          (conjugate_le_sup_of_quotient B X Y a ha.le)⟩
      letI := finiteIndex_of_finite_supplement N H hsH
      letI := finiteIndex_of_finite_supplement N K hsK
      exact conjugate_of_mutual_inclusions_finiteIndex H K (inclusion H K hK hsH hqA hqB)
        (inclusion K H hH hsK hqA.symm hqB.symm)

/-- Proposition 3.2 (`prop:thm_main_n_nilpotent`): Theorem 1.1 for finite `N`.
Only the normal subgroup is assumed finite; the ambient profinite group is arbitrary. -/
theorem proposition_3_2 {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  letI := pronilpotent_iff_nilpotent.mp hpron
  exact ⟨locallyConjugate_of_conjugate H K hH,
    finite_kernel_conjugacy_aux (Nat.card N) N H K rfl hN hH hK hcase hHN hKN⟩

end LocalConjugacy
