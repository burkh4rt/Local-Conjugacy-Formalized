module

public import LocalConjugacy.ProfiniteSylow

@[expose] public section

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]

theorem supersolvable_of_surjective (hG : Supersolvable G) (f : G →* F)
    (hs : Function.Surjective f) : Supersolvable F := by
  obtain ⟨n, s, h0, hn, hm, hnorm, hstep⟩ := hG
  refine ⟨n, fun i => (s i).map f, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0, Subgroup.map_bot]
  · dsimp only
    rw [hn, Subgroup.map_top_of_surjective f hs]
  · exact fun i j hij => Subgroup.map_mono (hm hij)
  · intro i
    letI := hnorm i
    exact (hnorm i).map f hs
  · intro i hi
    obtain ⟨x, hx⟩ := hstep i hi
    refine ⟨f x, ?_⟩
    dsimp only
    rw [hx, Subgroup.map_sup, MonoidHom.map_zpowers]

theorem supersolvable_of_mulEquiv (hG : Supersolvable G) (e : G ≃* F) :
    Supersolvable F := supersolvable_of_surjective hG e.toMonoidHom e.surjective

end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)

/-- A continuous discrete quotient of a prosupersolvable group is
supersolvable, with the actual normal cyclic series transported. -/
theorem supersolvable_of_prosupersolvable_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Supersolvable F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  exact supersolvable_of_surjective (hG U) (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)

theorem nilpotent_map (N : Subgroup G) (hN : Pronilpotent N)
    (f : G →* F) (hf : Continuous f) : Group.IsNilpotent (N.map f) := by
  let φ : N →* N.map f := (f.comp N.subtype).codRestrict (N.map f)
    (fun x => Subgroup.mem_map_of_mem f x.property)
  apply nilpotent_of_pronilpotent_surjective hN φ
    ((hf.comp continuous_subtype_val).subtype_mk _)
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem pronilpotent_iff_nilpotent : Pronilpotent G ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    exact nilpotent_of_pronilpotent_surjective h (MonoidHom.id G) continuous_id Function.surjective_id
  · intro h
    letI := h
    intro U
    infer_instance

theorem prosupersolvable_iff_supersolvable : Prosupersolvable G ↔ Supersolvable G := by
  constructor
  · intro h
    exact supersolvable_of_prosupersolvable_surjective h (MonoidHom.id G)
      continuous_id Function.surjective_id
  · intro h U
    exact supersolvable_of_surjective h (QuotientGroup.mk' U.toSubgroup)
      (QuotientGroup.mk'_surjective U.toSubgroup)

end Discrete
end LocalConjugacy
