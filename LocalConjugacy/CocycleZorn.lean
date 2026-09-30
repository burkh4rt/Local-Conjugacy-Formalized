module

public import LocalConjugacy.CocycleNeighborhood
public import LocalConjugacy.InvariantRestriction

@[expose] public section

namespace LocalConjugacy

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]

/-- A descending chain of closed subgroups eventually lies in every open set
containing its intersection. Chains need not be countable. -/
theorem exists_chain_member_subset_open (c : Set (Subgroup J)) (hne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) (hclosed : ∀ H ∈ c, IsClosed (H : Set J))
    (O : Set J) (hO : IsOpen O) (hsub : ((sInf c : Subgroup J) : Set J) ⊆ O) :
    ∃ H ∈ c, (H : Set J) ⊆ O := by
  classical
  letI : Nonempty c := hne.to_subtype
  have hd : Directed (· ⊇ ·) (fun H : c => (H.val : Set J)) := by
    intro H K
    rcases hc.total H.property K.property with h | h
    · exact ⟨H, le_rfl, h⟩
    · exact ⟨K, h, le_rfl⟩
  have hempty : Oᶜ ∩ (⋂ H : c, (H.val : Set J)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hi⟩
    apply hx (hsub ?_)
    exact Subgroup.mem_sInf.mpr (fun H hH => Set.mem_iInter.mp hi ⟨H, hH⟩)
  obtain ⟨H, hH⟩ := hO.isClosed_compl.isCompact.elim_directed_family_closed
    (fun H : c => (H.val : Set J)) (fun H => hclosed H H.property)
    (Set.disjoint_iff_inter_eq_empty.mpr hempty) hd
  refine ⟨H, H.property, fun x hx => ?_⟩
  by_contra hn
  exact Set.disjoint_left.mp hH hn hx

/-- Zorn's lemma for a property of closed intermediate subgroups that survives
nonempty descending chains. The starting subgroup is the whole ambient group. -/
theorem exists_minimal_closed_subgroup_of_chain_condition
    (P : Subgroup J) (bad : Subgroup J → Prop) (hbad : bad ⊤)
    (hchain : ∀ c : Set (Subgroup J), c.Nonempty → IsChain (· ≤ ·) c →
      (∀ H ∈ c, IsClosed (H : Set J) ∧ P ≤ H ∧ bad H) → bad (sInf c)) :
    ∃ L, Minimal (fun H : Subgroup J => IsClosed (H : Set J) ∧ P ≤ H ∧ bad H) L := by
  classical
  let S : Set (Subgroup J) := {H | IsClosed (H : Set J) ∧ P ≤ H ∧ bad H}
  have hb : ∀ c : Set (Subgroup J), c ⊆ S → IsChain (· ≤ ·) c →
      ∃ L ∈ S, ∀ H ∈ c, L ≤ H := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with he | hn
    · subst c
      exact ⟨⊤, ⟨isClosed_univ, le_top, hbad⟩, by simp⟩
    · refine ⟨sInf c, ⟨?_, ?_, hchain c hn hc hcs⟩,
        fun H hH => sInf_le hH⟩
      · rw [Subgroup.coe_sInf]
        exact isClosed_biInter (fun H hH => (hcs hH).1)
      · exact le_sInf (fun H hH => (hcs hH).2.1)
  exact (@zorn_le₀ (Subgroup J)ᵒᵈ _ S) (fun c hcs hc => hb c hcs hc.symm)

end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- A cocycle's cohomology class extends to a specified intermediate subgroup. -/
def Cocycle.ExtendsTo {P : Subgroup J} (f : Cocycle (N := N) P) (H : Subgroup J) : Prop :=
  ∃ (hPH : P ≤ H) (F : Cocycle (N := N) H), RestrictsTo hPH F f

theorem Cocycle.extendsTo_self {P : Subgroup J} (f : Cocycle (N := N) P) :
    f.ExtendsTo P := ⟨le_rfl, f, 1, by simp⟩

/-- An extension restricts to any intermediate subgroup containing the original domain. -/
theorem Cocycle.ExtendsTo.of_le {P H K : Subgroup J} {f : Cocycle (N := N) P}
    (h : f.ExtendsTo K) (hPH : P ≤ H) (hHK : H ≤ K) : f.ExtendsTo H := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPH, restrictCocycle hHK F, n, hn⟩

end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- If a fixed pair of global cocycles becomes cohomologous on a chain's
intersection, it is already cohomologous on one member of the chain. -/
theorem cohomologous_on_chain_intersection
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (c : Set (Subgroup J)) (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hclosed : ∀ H ∈ c, IsClosed (H : Set J))
    (hfg : Cohomologous (restrictCocycle (show sInf c ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g)) :
    ∃ H ∈ c, Cohomologous (restrictCocycle (show H ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g) := by
  obtain ⟨n, hn⟩ := hfg
  let E : Set J := {x | g.toFun ⟨x, trivial⟩ =
    n⁻¹ * f.toFun ⟨x, trivial⟩ * (x • n)}
  have he : IsOpen E := by
    have htop : Continuous (fun x : J => (⟨x, trivial⟩ : (⊤ : Subgroup J))) :=
      continuous_id.subtype_mk _
    have ht : Continuous (fun x : J =>
        (g.toFun ⟨x, trivial⟩, f.toFun ⟨x, trivial⟩, x • n)) :=
      (g.continuous_toFun.comp htop).prodMk
        ((f.continuous_toFun.comp htop).prodMk (continuous_id.smul continuous_const))
    exact ht.isOpen_preimage
      {t : N × N × N | t.1 = n⁻¹ * t.2.1 * t.2.2} (isOpen_discrete _)
  have hs : ((sInf c : Subgroup J) : Set J) ⊆ E := fun x hx => hn ⟨x, hx⟩
  obtain ⟨H, hH, hHE⟩ := exists_chain_member_subset_open c hne hc hclosed E he hs
  exact ⟨H, hH, n, fun x => hHE x.property⟩

/-- Zorn supplies an inclusion-minimal closed intermediate subgroup on which a fixed
failure of injectivity persists. Minimality concerns this pair of cocycles. -/
theorem exists_minimal_injectivity_counterexample
    (P : Subgroup J) (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hP : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g)) (hbad : ¬ Cohomologous f g) :
    ∃ L : Subgroup J, IsClosed (L : Set J) ∧ P < L ∧
      ¬ Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f)
        (restrictCocycle le_top g) ∧
      ∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L →
        Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
          (restrictCocycle le_top g) := by
  classical
  let bad : Subgroup J → Prop := fun H =>
    ¬ Cohomologous (restrictCocycle (show H ≤ ⊤ from le_top) f) (restrictCocycle le_top g)
  have hb : bad ⊤ := hbad
  obtain ⟨L, hL⟩ := exists_minimal_closed_subgroup_of_chain_condition P bad hb (by
    intro c hn hc hh hgood
    obtain ⟨H, hH, hfg⟩ := cohomologous_on_chain_intersection f g c hn hc
      (fun H hH => (hh H hH).1) hgood
    exact (hh H hH).2.2 hfg)
  refine ⟨L, hL.1.1, lt_of_le_of_ne hL.1.2.1 ?_, hL.1.2.2, ?_⟩
  · intro he
    exact hL.1.2.2 (he ▸ hP)
  · intro K hK hPK hKL
    by_contra hfg
    exact hL.not_prop_of_lt hKL ⟨hK, hPK, hfg⟩

/-- If a fixed cocycle class extends to the intersection of a descending
chain, it extends to one member. The proof extends a representative to an
open neighborhood subgroup, so it permits infinite discrete coefficients. -/
theorem extendsTo_on_chain_intersection {P : Subgroup J} (f : Cocycle (N := N) P)
    (c : Set (Subgroup J)) (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hclosed : ∀ H ∈ c, IsClosed (H : Set J)) (hP : ∀ H ∈ c, P ≤ H)
    (hf : f.ExtendsTo (sInf c)) : ∃ H ∈ c, f.ExtendsTo H := by
  have hi : IsClosed ((sInf c : Subgroup J) : Set J) := by
    rw [Subgroup.coe_sInf]
    exact isClosed_biInter hclosed
  obtain ⟨hPi, F, hF⟩ := hf
  obtain ⟨V, hVi, hV, G, hG⟩ := extend_cocycle_to_open_subgroup (sInf c) hi F
  have hfV : f.ExtendsTo V := by
    refine ⟨hPi.trans hVi, G, ?_⟩
    change Cohomologous (restrictCocycle (hPi.trans hVi) G) f
    change Cohomologous (restrictCocycle hPi (restrictCocycle hVi G)) f
    rw [hG]
    exact hF
  obtain ⟨H, hH, hHV⟩ := exists_chain_member_subset_open c hne hc hclosed V hV hVi
  exact ⟨H, hH, hfV.of_le (hP H hH) hHV⟩

/-- Zorn supplies an inclusion-minimal closed intermediate subgroup to which a fixed
cocycle class does not extend. Ambient stability, when present, is retained
by every intermediate subgroup. -/
theorem exists_minimal_surjectivity_counterexample
    (P : Subgroup J) (f : Cocycle (N := N) P) (hbad : ¬ f.ExtendsTo ⊤) :
    ∃ L : Subgroup J, IsClosed (L : Set J) ∧ P < L ∧ ¬ f.ExtendsTo L ∧
      ∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L → f.ExtendsTo K := by
  classical
  obtain ⟨L, hL⟩ := exists_minimal_closed_subgroup_of_chain_condition P
    (fun H => ¬ f.ExtendsTo H) hbad (by
      intro c hn hc hh hgood
      obtain ⟨H, hH, hf⟩ := extendsTo_on_chain_intersection f c hn hc
        (fun H hH => (hh H hH).1) (fun H hH => (hh H hH).2.1) hgood
      exact (hh H hH).2.2 hf)
  refine ⟨L, hL.1.1, lt_of_le_of_ne hL.1.2.1 ?_, hL.1.2.2, ?_⟩
  · intro he
    exact hL.1.2.2 (he ▸ f.extendsTo_self)
  · intro K hK hPK hKL
    by_contra hf
    exact hL.not_prop_of_lt hKL ⟨hK, hPK, hf⟩

/-- The fixed-pair Zorn induction principle. A proof for an intermediate
subgroup may use cohomology of this pair on all smaller intermediate subgroups. -/
theorem cohomologous_of_zorn_step
    (P : Subgroup J) (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hP : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g))
    (step : ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
      (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L →
        Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
          (restrictCocycle le_top g)) →
      Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f)
        (restrictCocycle le_top g)) : Cohomologous f g := by
  classical
  by_contra hbad
  obtain ⟨L, hL, hPL, hfg, hmin⟩ := exists_minimal_injectivity_counterexample P f g hP hbad
  exact hfg (step L hL hPL hmin)

/-- The fixed-class Zorn induction principle. It assumes extension only for
this class on smaller subgroups, never full surjectivity on those subgroups. -/
theorem extendsTo_of_zorn_step
    (P : Subgroup J) (f : Cocycle (N := N) P)
    (step : ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
      (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L → f.ExtendsTo K) →
      f.ExtendsTo L) : f.ExtendsTo ⊤ := by
  classical
  by_contra hbad
  obtain ⟨L, hL, hPL, hf, hmin⟩ := exists_minimal_surjectivity_counterexample P f hbad
  exact hf (step L hL hPL hmin)

/-- Restriction is an isomorphism once the two pointwise Zorn steps are supplied.
The remaining structural group theory is isolated in `injectivity_step` and
`surjectivity_step`. This is an induction principle, not the full Lemma 1.2. -/
theorem restrictionIsomorphism_of_zorn_steps
    (P : Subgroup J)
    (injectivity_step : ∀ f g : Cocycle (N := N) (⊤ : Subgroup J),
      Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f) (restrictCocycle le_top g) →
      ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
        (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L →
          Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
            (restrictCocycle le_top g)) →
        Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f)
          (restrictCocycle le_top g))
    (surjectivity_step : ∀ f : Cocycle (N := N) P, InvariantUnder ⊤ P f →
      ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
        (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L → f.ExtendsTo K) →
        f.ExtendsTo L) : RestrictionIsomorphism (N := N) ⊤ P le_top := by
  constructor
  · intro f g hfg
    exact cohomologous_of_zorn_step P f g hfg (injectivity_step f g hfg)
  · intro f hf
    obtain ⟨_, F, hF⟩ := extendsTo_of_zorn_step P f (surjectivity_step f hf)
    exact ⟨F, hF⟩

end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- After injectivity has been established, any lift of an ambient-invariant
class on a normal subgroup is itself ambient-invariant. Unlike Proposition
2.3, this step needs no surjectivity theorem for the intermediate subgroup. -/
theorem invariant_lift_of_injective_restriction
    (L K : Subgroup J) [L.Normal] [K.Normal] (hKL : K ≤ L)
    (hinj : ∀ f g : Cocycle (N := N) L,
      Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL g) → Cohomologous f g)
    (f : Cocycle (N := N) L) (g : Cocycle (N := N) K)
    (hg : InvariantUnder ⊤ K g) (hfg : RestrictsTo hKL f g) :
    InvariantUnder ⊤ L f := by
  rw [invariant_iff_twist]
  intro j
  apply hinj
  rw [restrict_twist]
  have hfg' : Cohomologous (restrictCocycle hKL f) g := hfg
  exact cohomologous_trans hfg' (cohomologous_trans
    ((invariant_iff_twist g).mp hg j)
    (cohomologous_symm (twist_cohomologous hfg' j)))

end Invariance
end LocalConjugacy
