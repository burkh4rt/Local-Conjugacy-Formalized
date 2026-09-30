module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed set of elements sending every element of `H` into `K`
by conjugation. -/
def transporter (H K : Subgroup G) : Set G :=
  {g | ∀ h ∈ H, g * h * g⁻¹ ∈ K}

theorem transporter_closed (H K : Subgroup G) (hK : IsClosed (K : Set G)) :
    IsClosed (transporter H K) := by
  unfold transporter
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun h => isClosed_iInter fun _ =>
    hK.preimage ((continuous_id.mul continuous_const).mul continuous_inv)

/-- The compactness step in Theorem 1.1. It applies to the paper's
`Hᵢ = (N ∩ Uᵢ)H` and `Kᵢ = (N ∩ Uᵢ)K` once the finite-quotient and
separation lemmas have been proved. All approximation hypotheses remain
explicit; this is not a claimed proof of Theorem 1.1 itself. -/
theorem conjugate_of_closed_approximations [CompactSpace G]
    {ι : Type*} [Nonempty ι] (H K : Subgroup G) (Hs Ks : ι → Subgroup G)
    (hHclosed : ∀ i, IsClosed (Hs i : Set G))
    (hKclosed : ∀ i, IsClosed (Ks i : Set G))
    (hHsep : ∀ x : G, (∀ i, x ∈ Hs i) → x ∈ H)
    (hKsep : ∀ x : G, (∀ i, x ∈ Ks i) → x ∈ K)
    (hdir : ∀ i j, ∃ k, Hs k ≤ Hs i ∧ Hs k ≤ Hs j ∧ Ks k ≤ Ks i ∧ Ks k ≤ Ks j)
    (hloc : ∀ i, ∃ g : G, g ∈ transporter H (Ks i) ∧ g⁻¹ ∈ transporter K (Hs i)) :
    Conjugate H K := by
  let T : ι → Set G := fun i => transporter H (Ks i) ∩ Inv.inv ⁻¹' transporter K (Hs i)
  have hclosed : ∀ i, IsClosed (T i) := fun i =>
    (transporter_closed H (Ks i) (hKclosed i)).inter
      ((transporter_closed K (Hs i) (hHclosed i)).preimage continuous_inv)
  have hnon : ∀ i, (T i).Nonempty := fun i => hloc i
  have hTdir : Directed (· ⊇ ·) T := by
    intro i j
    obtain ⟨k, hki, hkj, kki, kkj⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · intro g hg
      exact ⟨fun x hx => kki (hg.1 x hx), fun x hx => hki (hg.2 x hx)⟩
    · intro g hg
      exact ⟨fun x hx => kkj (hg.1 x hx), fun x hx => hkj (hg.2 x hx)⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hTdir hnon (fun i => (hclosed i).isCompact) hclosed
  have hg' : ∀ i, g ∈ T i := Set.mem_iInter.mp hg
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hKsep _ (fun i => (hg' i).1 x hx)
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · apply hHsep
      intro i
      simpa using (hg' i).2 y hy
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

end LocalConjugacy
