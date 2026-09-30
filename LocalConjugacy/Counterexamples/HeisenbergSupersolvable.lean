module

public import LocalConjugacy.Counterexamples.Heisenberg

@[expose] public section

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def diagonal : C3 →* G where
  toFun z := ⟨fun _ => z, 1⟩
  map_one' := rfl
  map_mul' := by intros; apply SemidirectProduct.ext <;> rfl

def Z : Subgroup G := diagonal.range
instance : DecidablePred (· ∈ Z) := fun x =>
  inferInstanceAs (Decidable (∃ z : C3, diagonal z = x))

instance : Z.Normal where
  conj_mem := by
    rintro _ ⟨z, rfl⟩ g
    have hc : ∀ z : C3, ∀ g : G, g * diagonal z * g⁻¹ = diagonal z := by decide
    rw [hc]
    exact ⟨z, rfl⟩

def baseSubgroup : Subgroup G := (SemidirectProduct.rightHom : G →* S).ker
instance : baseSubgroup.Normal := inferInstanceAs (SemidirectProduct.rightHom : G →* S).ker.Normal
instance : DecidablePred (· ∈ baseSubgroup) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))

def V : Subgroup G := N ⊓ baseSubgroup
instance : V.Normal := inferInstanceAs (N ⊓ baseSubgroup).Normal
instance : DecidablePred (· ∈ V) := fun x => inferInstanceAs
  (Decidable (x ∈ N ∧ x ∈ baseSubgroup))

def M : Subgroup G := (sign.comp (SemidirectProduct.rightHom : G →* S)).ker
instance : M.Normal := inferInstanceAs (sign.comp (SemidirectProduct.rightHom : G →* S)).ker.Normal
instance : DecidablePred (· ∈ M) := fun x => inferInstanceAs (Decidable (sign x.right = 1))

def v : G := ⟨fun i => Multiplicative.ofAdd (![1, 2, 0] i), 1⟩

private theorem step (L U : Subgroup G) (x : G) (n : ℕ)
    (hLU : L ≤ U) (hx : x ∈ U)
    (h : ∀ u ∈ U, ∃ k : Fin n, u * (x ^ k.val)⁻¹ ∈ L) :
    U = L ⊔ Subgroup.zpowers x := by
  apply le_antisymm _ (sup_le hLU (Subgroup.zpowers_le.mpr hx))
  intro u hu
  obtain ⟨k, hk⟩ := h u hu
  have ha : u * (x ^ k.val)⁻¹ ∈ L ⊔ Subgroup.zpowers x :=
    (show L ≤ L ⊔ Subgroup.zpowers x from le_sup_left) hk
  have hb : x ^ k.val ∈ L ⊔ Subgroup.zpowers x :=
    (show Subgroup.zpowers x ≤ L ⊔ Subgroup.zpowers x from le_sup_right)
      (Subgroup.npow_mem_zpowers x k.val)
  simpa using (L ⊔ Subgroup.zpowers x).mul_mem ha hb

theorem step_Z : Z = ⊥ ⊔ Subgroup.zpowers (diagonal (Multiplicative.ofAdd 1)) := by
  apply step ⊥ Z (diagonal (Multiplicative.ofAdd 1)) 3 bot_le
  · exact ⟨_, rfl⟩
  · exact (by decide : ∀ z ∈ Z, ∃ k : Fin 3,
      z * (diagonal (Multiplicative.ofAdd 1) ^ k.val)⁻¹ = 1)

theorem step_V : V = Z ⊔ Subgroup.zpowers v := by
  apply step _ _ _ 3
  · exact (by decide : ∀ x : G, x ∈ Z → x ∈ V)
  · decide
  · decide

theorem step_N : N = V ⊔ Subgroup.zpowers shift := by
  apply step _ _ _ 3
  · exact inf_le_left
  · decide
  · decide

theorem step_M : M = N ⊔ Subgroup.zpowers c := by
  apply step _ _ _ 3
  · exact (by decide : ∀ x : G, x ∈ N → x ∈ M)
  · decide
  · decide

theorem step_G : (⊤ : Subgroup G) = M ⊔ Subgroup.zpowers t := by
  apply step _ _ _ 2 le_top (Subgroup.mem_top _)
  intro u _
  exact (by decide : ∀ x : G, ∃ k : Fin 2, x * (t ^ k.val)⁻¹ ∈ M) u

/-- The invariant cyclic series has orders `1,3,9,27,81,162`. -/
theorem supersolvable_G : Supersolvable G := by
  let s : ℕ → Subgroup G := fun i =>
    if i = 0 then ⊥ else if i = 1 then Z else if i = 2 then V
    else if i = 3 then N else if i = 4 then M else ⊤
  have hs : ∀ i, s i ≤ s (i + 1) := by
    intro i
    by_cases hi : i < 5
    · interval_cases i
      · exact bot_le
      · change Z ≤ V; rw [step_V]; exact le_sup_left
      · change V ≤ N; rw [step_N]; exact le_sup_left
      · change N ≤ M; rw [step_M]; exact le_sup_left
      · exact le_top
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      have hi2 : i ≠ 2 := by omega
      have hi3 : i ≠ 3 := by omega
      have hi4 : i ≠ 4 := by omega
      have hj2 : i + 1 ≠ 2 := by omega
      have hj3 : i + 1 ≠ 3 := by omega
      have hj4 : i + 1 ≠ 4 := by omega
      simp [s, hi0, hi1, hi2, hi3, hi4, hj2, hj3, hj4]
  refine ⟨5, s, rfl, rfl, monotone_nat_of_le_succ hs, ?_, ?_⟩
  · intro i
    dsimp [s]
    split_ifs <;> infer_instance
  · intro i hi
    interval_cases i
    · exact ⟨diagonal (Multiplicative.ofAdd 1), step_Z⟩
    · exact ⟨v, step_V⟩
    · exact ⟨shift, step_N⟩
    · exact ⟨c, step_M⟩
    · exact ⟨t, step_G⟩

end LocalConjugacy.HeisenbergExample
