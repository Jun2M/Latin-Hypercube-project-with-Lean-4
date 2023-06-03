import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Linarith
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


lemma fin3_cases (x : Fin 3) : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
  rcases x with ⟨x, hx⟩
  have := Nat.zero_le x
  rcases Nat.lt_trichotomy x 0 with h1 | h2 | h3
  · -- x < 0
    exfalso ; clear hx
    exact Nat.lt_le_antisymm h1 this
  · -- x = 0
    left
    rw [← h2]
  · -- 0 < x
    right
    rcases Nat.lt_trichotomy x 1 with h4 | h5 | h6
    · -- x < 1
      exfalso ; clear hx this
      linarith
    · -- x = 1
      left
      rw [← h5]
    · -- 1 < x
      right
      rcases Nat.lt_trichotomy x 2 with h7 | h8 | h9
      · -- x < 2
        exfalso ; clear hx this h3
        linarith
      · -- x = 2
        rw [← h8]
      · -- 2 < x
        exfalso ; clear this h3 h6
        linarith
  done


-- Define latin squares as a set of triples (i, j, k) where i, j, k are in [0, len)
-- i is the row, j is the column, and k is the value
structure Lsq {len : Nat} (A : Set (Fin 3 → Fin len)) :=
  (nonempty : len > 0)
  (entries : ∀ i : Fin len, ∀ j : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 0 = i ∧ a 1 = j)
  (rows : ∀ j : Fin len, ∀ k : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 1 = j ∧ a 2 = k)
  (cols : ∀ k : Fin len, ∀ i : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 0 = i ∧ a 2 = k)


def is_LsqS {len : Nat} (A : Set (Fin 3 → Fin len)) : Prop := 
  (len > 0) ∧ 
  (∀ i : Fin len, ∀ j : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 0 = i ∧ a 1 = j) ∧
  (∀ j : Fin len, ∀ k : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 1 = j ∧ a 2 = k) ∧ 
  (∀ k : Fin len, ∀ i : Fin len, ∃! a : Fin 3 → Fin len, a ∈ A ∧ a 0 = i ∧ a 2 = k)


-- Define the set of all latin squares of size len
def LsqS_set (len : Nat) : Set (Set (Fin 3 → Fin len)) := 
  {A : Set (Fin 3 → Fin len) | is_LsqS A}


theorem row_perm {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_LsqS A) (σ : Fin len ≃ Fin len) : 
  is_LsqS {b : Fin 3 → Fin len | ∃ a : Fin 3 → Fin len, a ∈ A ∧ b = λ x => if x = 0 then σ (a 0) else a x} := by
  constructor
  · -- 1. nonempty
    exact HA.1

  · --
    constructor
    · -- 2. entries
      intro i j
      rcases (HA.2.1 (σ.symm i) j) with ⟨ a', ha'1, ha'2 ⟩
      use λ x => if x = 0 then σ (a' 0) else a' x
      constructor
      · -- 2.1 exists
        simp only [Set.mem_setOf_eq, ite_true, ite_false]
        refine ⟨ ?_, (by rw [ha'1.2.1, Equiv.apply_symm_apply]), (by rw [ha'1.2.2]) ⟩
        {
          use a'
          simp only [and_true]
          exact ha'1.1
          done
        }
      · -- 2.2 unique
        simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
        rintro a1 a2 ha2 ha1 rfl rfl
        rw [ha1]

        have : a2 = a' := by
          have := ha'2 a2 
          rw [and_imp, and_imp] at this

          have hh: a2 0 = σ.symm (a1 0) := by
            rw [ha1]
            simp only [ite_true, Equiv.symm_apply_apply]
            done

          have hh2 : a2 1 = a1 1 := by 
            rw [ha1]
            simp only [ite_false]
            done

          exact this ha2 hh hh2

        rw [this]
      done

    · --
      constructor
      · -- 3. rows
        intro j k
        rcases (HA.2.2.1 j k) with ⟨ a', ha'1, ha'2 ⟩
        use λ x => if x = 0 then σ (a' 0) else a' x
        constructor
        · -- 3.1 exists
          simp only [Set.mem_setOf_eq, ite_false]
          refine ⟨ ?_, ha'1.2.1, ha'1.2.2 ⟩
          use a'
          refine ⟨ ha'1.1, (by simp only) ⟩
        · -- 3.2 unique
          simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
          rintro a1 a2 ha2 ha1 rfl rfl
          rw [ha1]
          have : a2 = a' := by
            have := ha'2 a2 
            rw [and_imp, and_imp] at this

            have hh: (a2 1 = a1 1) ∧ (a2 2 = a1 2) := by
              rw [ha1]
              simp only [ite_false]
              done

            exact this ha2 hh.1 hh.2

          rw [this]
        done

      · -- 4. cols
        intro k i
        rcases (HA.2.2.2 k (σ.symm i)) with ⟨ a', ha'1, ha'2 ⟩
        use λ x => if x = 0 then σ (a' 0) else a' x
        constructor
        · -- 4.1 exists
          simp only [Set.mem_setOf_eq, ite_true]
          refine ⟨ ?_, (by rw [ha'1.2.1, Equiv.apply_symm_apply]), ha'1.2.2 ⟩
          use a'
          exact ⟨ ha'1.1, (by simp only) ⟩
        · -- 4.2 unique
          simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
          rintro a1 a2 ha2 ha1 rfl rfl
          rw [ha1]
          have : a2 = a' := by
            have := ha'2 a2 
            rw [and_imp, and_imp] at this

            have hh: (a2 0 = σ.symm (a1 0)) ∧ (a2 2 = a1 2) := by
              rw [ha1]
              simp only [ite_true, Equiv.symm_apply_apply, ite_false, and_self]
              done

            exact this ha2 hh.1 hh.2

          rw [this]
        done
  done


theorem axis_perm_long {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_LsqS A) (σ : Fin 3 ≃ Fin 3) :
  is_LsqS {b : Fin 3 → Fin len | ∃ a ∈ A , b = a ∘ σ } := by
  constructor
  · -- 1. nonempty
    exact HA.1

  · --
    constructor
    · -- 2. entries
      intro i j
      rcases (HA.2.1 i j) with ⟨ a', ⟨ ha'1, rfl, rfl ⟩, ha'2 ⟩
      use a'
      constructor
      · -- 2.1 exists
        simp
        
        have : a' ∘ ↑σ ∈ { b | ∃ a, a ∈ A ∧ b = a ∘ ↑σ } := by
          use a
          exact ⟨ ha1, rfl ⟩
        use this
        exact ⟨ hk1, rfl ⟩
      · -- 2.2 unique
        intro k' hk'
        rcases hk' with ⟨ k'', i', j', H, rfl, rfl, rfl ⟩
        apply hk2
        exact H
      done

    · --
      constructor
      · -- 3. rows
        intro j k
        rcases (HA.2.2.1 k j) with ⟨ i, hi1, hi2 ⟩
        use i
        constructor
        · -- 3.1 exists
          use i
          use j
          use k
          exact ⟨ hi1, rfl ⟩
        · -- 3.2 unique
          intro i' hi'
          rcases hi' with ⟨ i'', j', k', H, rfl, rfl, rfl ⟩
          apply hi2
          exact H
        done

      · -- 4. cols
        intro k i
        rcases (HA.2.2.2 i k) with ⟨ j, hj1, hj2 ⟩
        use j
        constructor
        · -- 4.1 exists
          use k
          use i
          use j
          exact ⟨ hj1, rfl ⟩
        · -- 4.2 unique
          intro j' hj'
          rcases hj' with ⟨ k', i', j'', H, rfl, rfl, rfl ⟩
          apply hj2
          exact H
        done
  done
