import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


-- Define latin squares as a set of triples (i, j, k) where i, j, k are in [0, len)
-- i is the row, j is the column, and k is the value
structure LsqS {len : Nat} (A : Set (Fin len × Fin len × Fin len)) :=  
  (nonempty : len > 0)
  (entries : ∀ i : Fin len, ∀ j : Fin len, ∃! k : Fin len, (i, j, k) ∈ A)
  (rows : ∀ j : Fin len, ∀ k : Fin len, ∃! i : Fin len, (i, j, k) ∈ A)
  (cols : ∀ k : Fin len, ∀ i : Fin len, ∃! j : Fin len, (i, j, k) ∈ A)


def is_LsqS {len : Nat} (A : Set (Fin len × Fin len × Fin len)) : Prop := 
  (len > 0) ∧ 
  (∀ i : Fin len, ∀ j : Fin len, ∃! k : Fin len, (i, j, k) ∈ A) ∧ 
  (∀ j : Fin len, ∀ k : Fin len, ∃! i : Fin len, (i, j, k) ∈ A) ∧ 
  (∀ k : Fin len, ∀ i : Fin len, ∃! j : Fin len, (i, j, k) ∈ A)


-- Define latin squares as a function from (i, j) to k
structure LsqF {len : Nat} (A : Fin len → Fin len → Fin len) :=
  (nonempty : len > 0)
  (entries : ∀ i : Fin len, ∀ j : Fin len, ∃! k : Fin len, A i j = k)
  (rows : ∀ j : Fin len, ∀ k : Fin len, ∃! i : Fin len, A i j = k)
  (cols : ∀ k : Fin len, ∀ i : Fin len, ∃! j : Fin len, A i j = k)


-- Define the set of all latin squares of size len
def LsqS_set (len : Nat) : Set (Set (Fin len × Fin len × Fin len)) := 
  {A : Set (Fin len × Fin len × Fin len) | is_LsqS A}


theorem row_perm {len : Nat} {A : Set (Fin len × Fin len × Fin len)} (HA : is_LsqS A) (σ : Fin len ≃ Fin len) : 
  is_LsqS {a : Fin len × Fin len × Fin len | ∃ (i j k : Fin len), (i, j, k) ∈ A ∧ a = (σ i, j, k)} := by
  constructor
  · -- 1. nonempty
    exact HA.1

  · --
    constructor
    · -- 2. entries
      intro i j
      rcases (HA.2.1 (σ.symm i) j) with ⟨ k, hk1, hk2 ⟩
      use k
      constructor
      · -- 2.1 exists
        use σ.symm i
        use j
        use k
        exact ⟨ hk1, (by rw [Equiv.apply_symm_apply]) ⟩
      · -- 2.2 unique
        intro k' hk'
        rcases hk' with ⟨ i', j', k'', H, rfl, rfl, rfl ⟩
        apply hk2
        simp only [Equiv.symm_apply_apply]
        exact H
      done

    · --
      constructor
      · -- 3. rows
        intro j k
        rcases (HA.2.2.1 j k) with ⟨ i, hi1, hi2 ⟩
        use σ i
        constructor
        · -- 3.1 exists
          use i
          use j
          use k
          exact ⟨ hi1, rfl ⟩
        · -- 3.2 unique
          intro i' hi'
          rcases hi' with ⟨ i'', j', k', H, rfl, rfl, rfl ⟩
          congr
          apply hi2
          exact H
        done

      · -- 4. cols
        intro k i
        rcases (HA.2.2.2 k (σ.symm i)) with ⟨ j, hj1, hj2 ⟩
        use j
        constructor
        · -- 4.1 exists
          use (σ.symm i)
          use j
          use k
          exact ⟨ hj1, (by rw [Equiv.apply_symm_apply]) ⟩
        · -- 4.2 unique
          intro j' hj'
          rcases hj' with ⟨ i', j'', k', H, rfl, rfl, rfl ⟩
          apply hj2
          simp only [Equiv.symm_apply_apply]
          exact H
        done
  done

def permuting_axiswise {len : Nat} (A : Set (Fin 3 → Fin len)) (σ : Fin 3 ≃ Fin 3) : Set (Fin 3 → Fin len) :=
  {b : Fin 3 → Fin len | ∃ a ∈ A , b = a ∘ σ }

-- A is a set of triplets
-- There are S3 group of ways to permutes a triplet (e.g (2 3) permutes (i, j, k) to (i, k, j) and etc.)
-- I want to say given any σ ∈ S3, return {σ a | a ∈ A}
theorem axis_perm_long {len : Nat} {A : Set (Fin len × Fin len × Fin len)} (HA : is_LsqS A) (σ : Fin 3 ≃ Fin 3) :
  is_LsqS {a : Fin len × Fin len × Fin len | ∃ (i j k : Fin len), (i, j, k) ∈ A ∧ "σ permutes the triplet"} := by
  constructor
  · -- 1. nonempty
    exact HA.1

  · --
    constructor
    · -- 2. entries
      intro i j
      rcases (HA.2.1 i j) with ⟨ k, hk1, hk2 ⟩
      use k
      constructor
      · -- 2.1 exists
        use k
        use i
        use j
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
