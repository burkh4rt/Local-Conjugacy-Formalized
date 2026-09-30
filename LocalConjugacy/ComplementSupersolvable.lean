module

public import LocalConjugacy.ComplementConjugacy
public import LocalConjugacy.SupersolvableCoefficients

@[expose] public section

namespace LocalConjugacy

section Complement
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N K : Subgroup G) [N.Normal]

attribute [local instance] NonabelianComplement.conjugationAction

/-- Multiplication identifies the complement's conjugation semidirect product
with the ambient group. Only injectivity is needed for supersolvability. -/
def complementActionHom : ActionProduct K N →* G :=
  SemidirectProduct.lift N.subtype K.subtype (fun _ => by ext; rfl)

theorem complementActionHom_injective (hc : N.IsComplement' K) :
    Function.Injective (complementActionHom N K) := by
  intro x y h
  have he : (x.left, x.right) = (y.left, y.right) := hc.injective h
  exact SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he)

theorem complementActionHom_continuous : Continuous (complementActionHom N K) :=
  (continuous_subtype_val.comp actionProduct_continuous_left).mul
    (continuous_subtype_val.comp actionProduct_continuous_right)

theorem prosupersolvable_complement_action [Finite N] [DiscreteTopology N]
    (hK : IsClosed (K : Set G)) (hc : N.IsComplement' K) (hG : Prosupersolvable G) :
    Prosupersolvable (ActionProduct K N) := by
  letI := profinite_closed_subgroup K hK
  exact prosupersolvable_of_continuous_injective hG (complementActionHom N K)
    (complementActionHom_continuous N K) (complementActionHom_injective N K hc)

/-- The finite-coefficient complement argument used in Proposition 3.1. -/
theorem finite_complement_conjugacy (N H K : Subgroup G) [N.Normal] [DiscreteTopology N] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hNH : N ⊓ H = ⊥) (hNK : N ⊓ K = ⊥) :
    Conjugate H K ↔ LocallyConjugate H K := by
  rcases hcase with hG | hquot
  · refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
    letI := profinite_closed_subgroup K hK
    letI := profinite_closed_subgroup N hN
    have hsem := prosupersolvable_complement_action N K hK
      (isComplement'_of_supplements_inf N K hKN hNK) hG
    obtain ⟨n, hn⟩ := NonabelianComplement.local_inclusion_of_primary N H
      (isComplement'_of_supplements_inf N H hHN hNH) hN hH K hK
      (locallyContains_of_locallyConjugate H K hlocal)
      (fun P hP => primary_decomposition hpron (Or.inl hsem) P hP)
    have he := eq_of_supplements_le N H (conjugate (n : G) K)
      (supplements_conjugate N K hKN n) hNH hn
    refine ⟨(n : G)⁻¹, ?_⟩
    rw [← he, conjugate_inv_cancel]
  · exact proposition_3_1_of_pronilpotent_quotient N H K hN hH hK hpron
      hquot hHN hKN hNH hNK

/-- Proposition 3.1 (`prop:comps`) of arXiv v1, with finite N. -/
theorem proposition_3_1 (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hNH : N ⊓ H = ⊥) (hNK : N ⊓ K = ⊥) :
    Conjugate H K ↔ LocallyConjugate H K := by
  letI := profinite_closed_subgroup N hN
  letI : DiscreteTopology N := Finite.instDiscreteTopology
  exact finite_complement_conjugacy N H K hN hH hK hpron hcase hHN hKN hNH hNK

end Complement
end LocalConjugacy
