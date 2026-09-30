module

public import LocalConjugacy.SupersolvableStructure

@[expose] public section

namespace LocalConjugacy

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)

def subgroup : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (S U : Subgroup _).comap (QuotientGroup.mk' U.toSubgroup)

theorem mem_subgroup (x : G) :
    x ∈ subgroup S ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ S U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem subgroup_closed : IsClosed (subgroup S : Set G) := by
  rw [show (subgroup S : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (S U).carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup S x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (S U).carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hS

theorem map_transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (S U : Subgroup _).map (transition h) = (S V : Subgroup _) := by
  exact hS U V h

theorem mem_of_le {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : G)
    (hx : QuotientGroup.mk' U.toSubgroup x ∈ S U) :
    QuotientGroup.mk' V.toSubgroup x ∈ S V := by
  have hy := Subgroup.mem_map_of_mem (transition h) hx
  rw [map_transition S hS U V h] at hy
  exact hy

theorem map_subgroup (U : OpenNormalSubgroup G) :
    (subgroup S).map (QuotientGroup.mk' U.toSubgroup) = (S U : Subgroup _) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_subgroup S x).mp hx U
  · intro y hy
    let : Nonempty (OpenNormalSubgroup G) := ⟨U⟩
    let T : OpenNormalSubgroup G → Set G := fun V =>
      {x | QuotientGroup.mk' V.toSubgroup x ∈ S V ∧ QuotientGroup.mk' U.toSubgroup x = y}
    have hc : ∀ V, IsClosed (T V) := by
      intro V
      exact ((isClosed_discrete (S V).carrier).preimage
        (continuous_quotient_mk' : Continuous (QuotientGroup.mk' V.toSubgroup))).inter
        (isClosed_eq (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))
          continuous_const)
    have hn : ∀ V, (T V).Nonempty := by
      intro V
      have hymap : y ∈ (S (U ⊓ V)).map
          (transition (show U ⊓ V ≤ U from inf_le_left)) := by
        rwa [map_transition S hS (U ⊓ V) U inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hymap
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      exact ⟨x, mem_of_le S hS inf_le_right x hz, hzy⟩
    have hd : Directed (· ⊇ ·) T := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · intro x hx
        exact ⟨mem_of_le S hS inf_le_left x hx.1, hx.2⟩
      · intro x hx
        exact ⟨mem_of_le S hS inf_le_right x hx.1, hx.2⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn (fun V => (hc V).isCompact) hc
    have hx' : ∀ V, x ∈ T V := Set.mem_iInter.mp hx
    exact ⟨x, (mem_subgroup S x).mpr (fun V => (hx' V).1), (hx' U).2⟩


end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise

theorem subgroup_le_of_finite_images (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (h : ∀ U : OpenNormalSubgroup G,
      H.map (QuotientGroup.mk' U.toSubgroup) ≤ K.map (QuotientGroup.mk' U.toSubgroup)) :
    H ≤ K := by
  intro x hx
  apply mem_of_mem_sup_openNormal K hK x
  intro U
  have hm := h U (Subgroup.mem_map_of_mem (QuotientGroup.mk' U.toSubgroup) hx)
  change x ∈ (K.map (QuotientGroup.mk' U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup) at hm
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hm

theorem IsHallPro.le_normal {π : Set ℕ} {H K : Subgroup G} [K.Normal]
    (hH : IsHallPro π H) (hK : IsHallPro π K) : H ≤ K := by
  apply subgroup_le_of_finite_images H K hK.1
  intro U
  letI := (inferInstance : K.Normal).map (QuotientGroup.mk' U.toSubgroup)
    (QuotientGroup.mk'_surjective U.toSubgroup)
  exact ((hH.2 U).1).le_normalHall (hK.2 U)

theorem IsHallPro.eq_of_normal {π : Set ℕ} {H K : Subgroup G} [H.Normal] [K.Normal]
    (hH : IsHallPro π H) (hK : IsHallPro π K) : H = K :=
  le_antisymm (hH.le_normal hK) (hK.le_normal hH)

noncomputable def finiteUpperHall (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : Subgroup (G ⧸ U.toSubgroup) :=
  (supersolvable_exists_normalHall (hG U) n).choose

instance finiteUpperHall_normal (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : (finiteUpperHall hG n U).Normal :=
  (supersolvable_exists_normalHall (hG U) n).choose_spec.1

theorem finiteUpperHall_hall (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : IsHall {p | n < p} (finiteUpperHall hG n U) :=
  (supersolvable_exists_normalHall (hG U) n).choose_spec.2

theorem finiteUpperHall_transition (hG : Prosupersolvable G) (n : ℕ)
    (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (finiteUpperHall hG n U).map (transition h) = finiteUpperHall hG n V := by
  letI := (inferInstance : (finiteUpperHall hG n U).Normal).map
    (transition h) (transition_surjective h)
  exact ((finiteUpperHall_hall hG n U).map_surjective
    (transition h) (transition_surjective h)).eq_of_normal (finiteUpperHall_hall hG n V)

noncomputable def upperHall (hG : Prosupersolvable G) (n : ℕ) : Subgroup G :=
  FiniteSubgroupSystem.subgroup (finiteUpperHall hG n)

instance upperHall_normal (hG : Prosupersolvable G) (n : ℕ) : (upperHall hG n).Normal := by
  constructor
  intro x hx g
  apply (FiniteSubgroupSystem.mem_subgroup _ _).mpr
  intro U
  have hxU := (FiniteSubgroupSystem.mem_subgroup _ _).mp hx U
  simpa only [map_mul, map_inv] using
    (inferInstance : (finiteUpperHall hG n U).Normal).conj_mem _ hxU
      (QuotientGroup.mk' U.toSubgroup g)

theorem upperHall_isHallPro (hG : Prosupersolvable G) (n : ℕ) :
    IsHallPro {p | n < p} (upperHall hG n) := by
  refine ⟨FiniteSubgroupSystem.subgroup_closed _, fun U => ?_⟩
  change IsHall _ ((FiniteSubgroupSystem.subgroup _).map _)
  rw [FiniteSubgroupSystem.map_subgroup _ (finiteUpperHall_transition hG n)]
  exact finiteUpperHall_hall hG n U

namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)

def obj (U : OpenNormalSubgroup G) :=
  {Q : Subgroup (G ⧸ U.toSubgroup) //
    (finiteUpperHall hG n U).IsComplement' Q ∧ IsHall {r | r ≤ n} Q ∧
      P.map (QuotientGroup.mk' U.toSubgroup) ≤ Q}

def map {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (Q : obj hG n P U) : obj hG n P V := by
  refine ⟨Q.val.map (transition h), ?_, ?_, ?_⟩
  · have hh := complement_map_of_disjoint Q.property.1 (transition h) (transition_surjective h)
      (disjoint_of_cutoff_primes ((finiteUpperHall_hall hG n U).1.map (transition h))
        (Q.property.2.1.1.map (transition h)))
    rwa [finiteUpperHall_transition] at hh
  · exact Q.property.2.1.map_surjective (transition h) (transition_surjective h)
  · have hπ : (transition h).comp (QuotientGroup.mk' U.toSubgroup) =
        QuotientGroup.mk' V.toSubgroup := rfl
    rw [← hπ, ← Subgroup.map_map]
    exact Subgroup.map_mono Q.property.2.2

def functor : OpenNormalSubgroup G ⥤ Type _ where
  obj := obj hG n P
  map h := TypeCat.ofHom (map hG n P (leOfHom h))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    change Q.val.map (transition (le_refl U)) = Q.val
    rw [transition_refl, Subgroup.map_id]
  map_comp {U V W} h k := by
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    change Q.val.map (transition ((leOfHom h).trans (leOfHom k))) =
      (Q.val.map (transition (leOfHom h))).map (transition (leOfHom k))
    rw [Subgroup.map_map, transition_comp]

theorem exists_compatible {p : ℕ} [Fact p.Prime] (hpn : p ≤ n)
    (hP : IsSylowPro p ⊤ P) :
    ∃ Q : (U : OpenNormalSubgroup G) → obj hG n P U,
      ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
        (Q U).val.map (transition h) = (Q V).val := by
  let : ∀ U, Finite ((functor hG n P).obj U) := fun U => by
    change Finite (obj hG n P U)
    unfold obj
    infer_instance
  have hn (U : OpenNormalSubgroup G) : Nonempty (obj hG n P U) := by
    obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
    obtain ⟨Q, hQ, hQh, hSQ⟩ := supersolvable_hall_split_containing (hG U) hpn S
      (finiteUpperHall hG n U) (finiteUpperHall_hall hG n U)
    exact ⟨⟨Q, hQ, hQh, hS ▸ hSQ⟩⟩
  let : ∀ U, Nonempty ((functor hG n P).obj U) := hn
  obtain ⟨Q, hQ⟩ := nonempty_sections_of_finite_cofiltered_system (functor hG n P)
  exact ⟨Q, fun U V h => congrArg Subtype.val (hQ (homOfLE h))⟩

end HallComplementSystem

/-- The profinite Hall cutoff decomposition, including the requirement
that the complement contain a prescribed Sylow subgroup below the cutoff. -/
theorem prosupersolvable_hall_split_containing (hG : Prosupersolvable G)
    {n p : ℕ} [Fact p.Prime] (hpn : p ≤ n) (P : Subgroup G) (hP : IsSylowPro p ⊤ P) :
    ∃ M Q : Subgroup G, M.Normal ∧ IsHallPro {r | n < r} M ∧
      IsHallPro {r | r ≤ n} Q ∧ M.IsComplement' Q ∧ P ≤ Q := by
  classical
  obtain ⟨Qs, hQs⟩ := HallComplementSystem.exists_compatible hG n P hpn hP
  let M := upperHall hG n
  let Q := FiniteSubgroupSystem.subgroup (fun U => (Qs U).val)
  have hM := upperHall_isHallPro hG n
  have hQclosed : IsClosed (Q : Set G) := FiniteSubgroupSystem.subgroup_closed _
  have hMmap (U : OpenNormalSubgroup G) :
      M.map (QuotientGroup.mk' U.toSubgroup) = finiteUpperHall hG n U :=
    FiniteSubgroupSystem.map_subgroup _ (finiteUpperHall_transition hG n) U
  have hQmap (U : OpenNormalSubgroup G) : Q.map (QuotientGroup.mk' U.toSubgroup) = (Qs U).val :=
    FiniteSubgroupSystem.map_subgroup _ hQs U
  have hQHall : IsHallPro {r | r ≤ n} Q := by
    refine ⟨hQclosed, fun U => ?_⟩
    rw [hQmap]
    exact (Qs U).property.2.1
  have hPQ : P ≤ Q := by
    apply subgroup_le_of_finite_images P Q hQclosed
    intro U
    rw [hQmap]
    exact (Qs U).property.2.2
  have hd : Disjoint M Q := by
    apply disjoint_iff_inf_le.mpr
    apply subgroup_le_of_finite_images (M ⊓ Q) ⊥ (isClosed_singleton : IsClosed ({1} : Set G))
    intro U
    have hh := Subgroup.map_mono (show M ⊓ Q ≤ M from inf_le_left) (f := QuotientGroup.mk' U.toSubgroup)
    have hk := Subgroup.map_mono (show M ⊓ Q ≤ Q from inf_le_right) (f := QuotientGroup.mk' U.toSubgroup)
    rw [hMmap] at hh
    rw [hQmap] at hk
    rw [Subgroup.map_bot]
    exact (le_inf hh hk).trans (Qs U).property.1.disjoint.le_bot
  have hsupclosed : IsClosed ((M ⊔ Q : Subgroup G) : Set G) := by
    rw [Subgroup.normal_mul]
    exact hQclosed.mul_left_of_isCompact hM.1.isCompact
  have hsup : M ⊔ Q = ⊤ := by
    apply top_unique
    apply subgroup_le_of_finite_images ⊤ (M ⊔ Q) hsupclosed
    intro U
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup),
      Subgroup.map_sup, hMmap, hQmap, (Qs U).property.1.sup_eq_top]
  have hcomp : M.IsComplement' Q := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [← Subgroup.normal_mul, hsup]
    rfl
  exact ⟨M, Q, inferInstance, hM, hQHall, hcomp, hPQ⟩

end ProfiniteHall
end LocalConjugacy
