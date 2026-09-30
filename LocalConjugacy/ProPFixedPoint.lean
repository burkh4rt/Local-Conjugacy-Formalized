module

public import LocalConjugacy.ProfiniteSylow

@[expose] public section

namespace LocalConjugacy

/-- A pro-`p` group acting on a finite set with closed stabilizers has a
fixed point whenever the cardinality of the set is prime to `p`. -/
theorem proP_fixed_point {G Ω : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MulAction G Ω] [Finite Ω]
    {p : ℕ} [Fact p.Prime] (hG : IsProP p G)
    (hc : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hcard : ¬ p ∣ Nat.card Ω) : ∃ x : Ω, ∀ g : G, g • x = x := by
  let ρ := MulAction.toPermHom G Ω
  have hk : IsClosed (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ x : Ω, (MulAction.stabilizer G x : Set G) := by
      ext g
      simp only [Set.mem_iInter, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
      change ρ g = 1 ↔ ∀ x, g • x = x
      exact Equiv.ext_iff
    rw [he]
    exact isClosed_iInter hc
  let U : OpenNormalSubgroup G :=
    { toSubgroup := ρ.ker
      isOpen' := ρ.ker.isOpen_of_isClosed_of_finiteIndex hk }
  have hr : IsPGroup p ρ.range := (hG U).of_equiv (QuotientGroup.quotientKerEquivRange ρ)
  letI : MulAction ρ.range Ω := MulAction.compHom Ω ρ.range.subtype
  obtain ⟨x, hx⟩ := hr.nonempty_fixed_point_of_prime_not_dvd_card Ω hcard
  refine ⟨x, fun g => ?_⟩
  exact hx ⟨ρ g, ⟨g, rfl⟩⟩

end LocalConjugacy
