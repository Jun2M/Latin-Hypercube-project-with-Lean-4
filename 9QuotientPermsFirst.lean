import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.NthRewrite
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


-- Main source : http://users.cecs.anu.edu.au/~bdm/papers/hypercubes.pdf

/-
1. Define the hypercube as a set of functions from Fin d to Fin n
2. Define a blind transformations on hypercubes
3. Quotient the permutations (input of transformation) s.t. the transformation is injective
4. Define a transformation on the quotient
5. Show that the transformation on the quotient are bijective
6. Show that the set of transformations under multiplication is a group
-/


/- 
Define latin hypercubes as a set of functions from Fin d to Fin n
latin is defined as in for any line in [n]ᵈ⁺¹, there is a unique point in A on that line
NOTE : contrary to the convention, we use 0-indexing here 
and the entry of a point is the 0th coordinate
-/

def is_LatinHypercube {n d : Nat} (A : Set (Fin d → Fin n)) : Prop := 
  if H0 : n > 0 ∧ d > 1 then 
    ∀ f : Fin d → Fin n, ∀ x : Fin d, ∃! a : Fin d → Fin n, a ∈ A ∧
      ∀ y : Fin d, x ≠ y → a y = f y 
  else 
    False

structure LatinHypercube (n d : Nat) :=
  (H0 : n > 0 ∧ d > 1)
  (set : Set (Fin d → Fin n))
  (prop : is_LatinHypercube set)

namespace LatinHypercube

-- Define Different types of transformations on latin hypercubes

def Isotopism {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : LatinHypercube n d) :
  LatinHypercube n d := ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => σₙd x (a x))}, by
    have := A.prop
    revert this
    unfold is_LatinHypercube
    simp only [gt_iff_lt, A.H0, and_self, ne_eq, dite_eq_ite, ite_true]

    rintro HA f x
    specialize HA (λ x => (σₙd x).symm (f x)) x
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => σₙd x (a' x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy'
        rw [ha'1.2 y' hy', Equiv.apply_symm_apply]
      done
    · -- 2.
      simp only [and_imp] ; clear ha'1
      rintro a1 ha1 ha1f
      rw [Set.mem_setOf_eq] at ha1
      rcases ha1 with ⟨a2, ha2, rfl⟩
      have : a2 = a' := by
        apply ha'2 ; clear ha'2 a'
        refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
        rintro y' hy'
        rw [← (ha1f y' hy'), Equiv.symm_apply_apply]
        done
      rw [this]
    done
    ⟩

def Isotopism.toEquiv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) : LatinHypercube n d ≃ LatinHypercube n d :=
  ⟨ Isotopism σₙd , Isotopism fun x => (σₙd x).symm, by
    unfold Function.LeftInverse Isotopism 
    rintro A
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
      simp only [Equiv.symm_apply_apply]
      exact hf
    · -- 2.
      rintro hf
      use λ x => (σₙd x) (f x)
      simp only [Equiv.symm_apply_apply, and_true]
      exact ⟨ f, hf, rfl ⟩
    done
  , by 
    unfold Function.RightInverse Function.LeftInverse Isotopism
    rintro A
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
      simp only [Equiv.apply_symm_apply]
      exact hf
    · -- 2.
      rintro hf
      use λ x => (σₙd x).symm (f x)
      simp only [Equiv.apply_symm_apply, and_true]
      exact ⟨ f, hf, rfl ⟩
    done
  ⟩


structure IsoAsObject {n d : Nat} :=
  (f : LatinHypercube n d → LatinHypercube n d)
  

noncomputable instance IsoGroup {n d : Nat} (H0 : n > 0 ∧ d > 1) : Group (Isotopism) := by
  refine'
  {
    mul := Isotopism.mul

    one := Isotopism.one H0

    inv := Isotopism.inv

    div := fun g h => Isotopism.mul h.inv g
    
    npow := @npowRec _ ⟨Isotopism.one H0⟩ ⟨fun g h => Isotopism.mul h g⟩
    zpow := @zpowRec _ ⟨Isotopism.one H0⟩ ⟨fun g h => Isotopism.mul h g⟩ ⟨Isotopism.inv⟩
    .. } <;>
  intros <;>
  ext <;>
  try rfl
  apply Equiv.left_inv