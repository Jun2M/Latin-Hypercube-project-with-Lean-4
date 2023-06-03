import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Contrapose
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


-- Main source : http://users.cecs.anu.edu.au/~bdm/papers/hypercubes.pdf


-- lemma fin3_cases (x : Fin 3) : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
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

-- structure Lsq {len : Nat} (A : Set (Fin 3 → Fin len)) :=
--   (nontrivial : len > 0)
--   (latin : ∀ f : Fin 3 → Fin len, ∀ x : Fin 3, ∃! a : Fin 3 → Fin len, a ∈ A ∧ ∀ y : Fin 3, x ≠ y → a y = f y )


-- Define latin squares as a set of functions from Fin 3 to Fin len
-- latin is defined as in for any line in [n]ᵈ⁺¹, there is a unique point in A on that line
def is_Lsq {len : Nat} (A : Set (Fin 3 → Fin len)) : Prop := 
  (len > 0) ∧ (∀ f : Fin 3 → Fin len, ∀ x : Fin 3, ∃! a : Fin 3 → Fin len, a ∈ A ∧ ∀ y : Fin 3, x ≠ y → a y = f y )


-- Define the set of all latin squares of size len
def Lsq_set (len : Nat) : Set (Set (Fin 3 → Fin len)) := 
  {A : Set (Fin 3 → Fin len) | is_Lsq A}


-- Define reduced latin squares 
def is_reduced {len : Nat} (A : Set (Fin 3 → Fin len)) : Prop := 
  is_Lsq A ∧ ∀ x : Fin 3, ∃ a : Fin 3 → Fin len, a ∈ A ∧ (∀ y : Fin 3, x ≠ y → x ≠ 2 → a y = (0 : Fin 3)) ∧ (a x = a 2)


def RLsq_set (len : Nat) : Set (Set (Fin 3 → Fin len)) := 
  {A : Set (Fin 3 → Fin len) | is_reduced A}


-- Defining paratopisms

-- Proof Strategy :
-- f                         Profit!
-- |                           ↑
--undo permunation         permutation
-- ↓                           |
-- f'  -Find the point in A →  a'

theorem row_perm {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_Lsq A) (σₙ : Fin len ≃ Fin len) : 
  is_Lsq {b : Fin 3 → Fin len | ∃ a : Fin 3 → Fin len, a ∈ A ∧ b = λ x => if x = 0 then σₙ (a 0) else a x} := by
  refine ⟨HA.1, ?_⟩
  intro f x
  -- f' = λ x => if x = 0 then σₙ.symm (f 0) else f x
  rcases HA.2 (λ x => if x = 0 then σₙ.symm (f 0) else f x) x with ⟨a', ha'1, ha'2⟩ ; clear HA
  -- a = λ x => if x = 0 then σₙ (a' 0) else a' x
  use λ x => if x = 0 then σₙ (a' 0) else a' x
  simp only [Set.mem_setOf_eq, ne_eq, and_imp, forall_exists_index]
  constructor
  · -- 1. exist
    clear ha'2
    constructor
    · -- 1-1 ∈ A
      use a'
      simp only [and_true, ha'1.1]
      done
    · -- 1-2 on the line through f
      intro y hy
      have := ha'1.2 y hy ; clear ha'1 hy x A
      by_cases h : y = 0
      ·
        rw [h] at this
        simp only [h, this, ite_true, Equiv.apply_symm_apply]
      · -- h : y ≠ 0
        simp only [h, this, ite_false]
      done
    done
  · -- 2. unique
    rintro a1 a2 ha2 rfl ha2f ; clear ha'1
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      intro y hy
      by_cases h : y = 0
      ·
        rw [← ha2f]
        simp only [h, ite_true, Equiv.symm_apply_apply]
        rw [h] at hy
        exact hy
        done
      · -- h : y ≠ 0
        specialize ha2f y hy ; clear hy
        simp only [h, ite_false] at ha2f
        simp only [ha2f, h, ite_false]
        done
      done
    rw [this]
    done
  done


theorem axis_perm {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_Lsq A) (σ₃ : Fin 3 ≃ Fin 3) :
  is_Lsq {b : Fin 3 → Fin len | ∃ a ∈ A , b = a ∘ σ₃ } := by
  refine ⟨HA.1, ?_⟩
  intro f x
  rcases HA.2 (f ∘ σ₃.symm) (σ₃ x) with ⟨a', ha'1, ha'2⟩ ; clear HA
  use a' ∘ σ₃
  simp only [Set.mem_setOf_eq, ne_eq, Function.comp_apply, and_imp, forall_exists_index]
  constructor
  · -- 1. exist
    constructor ; clear ha'2
    · -- 1-1 ∈ A
      use a'
      simp only [and_true]
      exact ha'1.1
      done
    · -- 1-2 on the line through f
      intro y hy

      have := ha'1.2 (σ₃ y) (?_) ; clear ha'1 ha'2 hy x A
      rw [this]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]

      intro h ; clear ha'1 ha'2 A a' f
      exact hy (σ₃.bijective.1 h)
      done
    done
  · -- 2. unique
    rintro a1 a2 ha2 rfl ha2f ; clear ha'1
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      intro y hy
      specialize ha2f (σ₃.symm y) (?_)
      {
        revert hy
        contrapose!
        intro h
        rw [h] ; clear h
        simp only [Equiv.apply_symm_apply]
      }

      simp only [Function.comp_apply, Equiv.apply_symm_apply] at ha2f
      exact ha2f
      done

    rw [this]
    done
  done

-- Column permutation and Entry permutation are just row permutation then axis permutation

theorem col_perm {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_Lsq A) (σₙ : Fin len ≃ Fin len) : 
  is_Lsq {b : Fin 3 → Fin len | ∃ a : Fin 3 → Fin len, a ∈ A ∧ b = λ x => if x = 1 then σₙ (a 1) else a x} := by
  refine ⟨ HA.1, ?_ ⟩
  intro f x
  rcases HA.2 (λ x => if x = 1 then σₙ.symm (f 1) else f x) x with ⟨a', ha'1, ha'2⟩ ; clear HA
  use λ x => if x = 1 then σₙ (a' 1) else a' x
  simp only [Set.mem_setOf_eq, ne_eq, and_imp, forall_exists_index]
  constructor
  · -- 1. exist
    clear ha'2
    constructor
    · -- 1-1 ∈ A
      use a'
      simp only [and_true, ha'1.1]
      done
    · -- 1-2 on the line through f
      intro y hy
      have := ha'1.2 y hy ; clear ha'1 hy x A
      by_cases h : y = 1
      ·
        rw [h] at this
        simp only [h, this, ite_true, Equiv.apply_symm_apply]
      · -- h : y ≠ 1
        simp only [h, this, ite_false]
      done
    done
  · -- 2. unique
    rintro a1 a2 ha2 rfl ha2f ; clear ha'1
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      intro y hy
      by_cases h : y = 1
      ·
        rw [← ha2f]
        simp only [h, ite_true, Equiv.symm_apply_apply]
        rw [h] at hy
        exact hy
        done
      · -- h : y ≠ 1
        specialize ha2f y hy ; clear hy
        simp only [h, ite_false] at ha2f
        simp only [ha2f, h, ite_false]
        done
      done
    rw [this]
    done
  done

theorem entry_perm {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_Lsq A) (σ₃ : Fin 3 ≃ Fin 3) :
  is_Lsq {b : Fin 3 → Fin len | ∃ a ∈ A , b = a ∘ σ₃ } := by
  refine ⟨HA.1, ?_⟩
  intro f x
  rcases HA.2 (f ∘ σ₃.symm) (σ₃ x) with ⟨a', ha'1, ha'2⟩ ; clear HA
  use a' ∘ σ₃
  simp only [Set.mem_setOf_eq, ne_eq, Function.comp_apply, and_imp, forall_exists_index]
  constructor
  · -- 1. exist
    constructor ; clear ha'2
    · -- 1-1 ∈ A
      use a'
      simp only [and_true]
      exact ha'1.1
      done
    · -- 1-2 on the line through f
      intro y hy

      have := ha'1.2 (σ₃ y) (?_) ; clear ha'1 ha'2 hy x A
      rw [this]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]

      intro h ; clear ha'1 ha'2 A a' f
      exact hy (σ₃.bijective.1 h)
      done
    done
  · -- 2. unique
    rintro a1 a2 ha2 rfl ha2f ; clear ha'1
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      intro y hy
      specialize ha2f (σ₃.symm y) (?_)
      {
        revert hy
        contrapose!
        intro h
        rw [h] ; clear h
        simp only [Equiv.apply_symm_apply]
      }

      simp only [Function.comp_apply, Equiv.apply_symm_apply] at ha2f
      exact ha2f
      done

    rw [this]
    done
  done


-- Define isomorphism of latin squares
theorem isomorphism {len : Nat} {A : Set (Fin 3 → Fin len)} (HA : is_Lsq A) (σₙ : Fin len ≃ Fin len) : 
  is_Lsq {b : Fin 3 → Fin len | ∃ a : Fin 3 → Fin len, a ∈ A ∧ b = σₙ ∘ a} := by
  refine ⟨HA.1, ?_⟩
  intro f x
  rcases HA.2 (σₙ.symm ∘ f) x with ⟨a', ha'1, ha'2⟩ ; clear HA
  use σₙ ∘ a'
  simp only [Set.mem_setOf_eq, ne_eq, Function.comp_apply, and_imp, forall_exists_index]
  constructor
  · -- 1. exist
    constructor ; clear ha'2
    · -- 1-1 ∈ A
      use a'
      simp only [and_true]
      exact ha'1.1
      done
    · -- 1-2 on the line through f
      intro y hy

      have := ha'1.2 y hy ; clear ha'1 ha'2 hy x A
      rw [this]
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    done
  · -- 2. unique
    rintro a1 a2 ha2 rfl ha2f ; clear ha'1
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      intro y hy
      specialize ha2f y hy
      rw [Function.comp_apply] at ha2f
      rw [Function.comp_apply, ← ha2f]
      simp only [Equiv.symm_apply_apply]
      done

    rw [this]
    done
  done




