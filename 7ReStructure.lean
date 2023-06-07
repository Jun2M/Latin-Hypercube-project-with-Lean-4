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

-- def 𝓗 (n d : Nat) := {_ : LatinHypercube n d}

-- Define Isotopism class
def Blindisotopism {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => σₙd x (a x))}

lemma Blindisotopism.main_imp {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (Blindisotopism σₙd A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1
  · -- 1.
    simp only [H0, if_true]
    intro HA f x
    specialize HA (λ x => (σₙd x).symm (f x)) x
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => σₙd x (a' x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        unfold Blindisotopism
        rw [Set.mem_setOf_eq]
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy'
        rw [ha'1.2 y' hy', Equiv.apply_symm_apply]
        done
      done

    · -- 2.
      simp only [and_imp] ; clear ha'1
      rintro a1 ha1 ha1f
      unfold Blindisotopism at ha1
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
    done
  · -- 2.
    simp only [H0, if_false]
  done

theorem Blindisotopism.main {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A ↔ is_LatinHypercube (Blindisotopism σₙd A) := by
  intro A
  constructor
  · -- 1.
    exact Blindisotopism.main_imp σₙd A
    done
  · -- 2.
    rintro HA
    have HA' := @Blindisotopism.main_imp n d (λ x => (σₙd x).symm) (Blindisotopism σₙd A) HA ; clear HA
    have : Blindisotopism (fun x => (σₙd x).symm) (Blindisotopism σₙd A) = A := by
      unfold Blindisotopism
      ext f
      simp
      constructor
      · -- 1.
        rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
        simp only [Equiv.symm_apply_apply]
        exact hf
      · -- 2.
        rintro hf
        use λ x => (σₙd x) (f x)
        constructor
        · exact ⟨ f, hf, rfl ⟩
        · simp only [Equiv.symm_apply_apply]
      done
    rw [← this]
    exact HA'
    done

class Isotopism (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (σₙd : Fin d → Fin n ≃ Fin n)
  (iso : toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => σₙd x (a x))}, Blindisotopism.main_imp σₙd A.set A.prop ⟩)
  (inv_iso : toEquiv.invFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => (σₙd x).symm (a x))}, 
      Blindisotopism.main_imp (λ x => (σₙd x).symm) A.set A.prop ⟩)
  

def Blindconjugate {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = a ∘ σ_d}

lemma conjugate.main_imp {n d : Nat} {H : 𝓗 n d} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) :
  A ∈ H.set → conjugate σ_d A ∈ H.set := by
  rw [H.prop, H.prop]
  unfold is_LatinHypercube
  simp only [gt_iff_lt, H.H0, and_self, ne_eq, dite_eq_ite, ite_true]

  rintro HA f x
  specialize HA (λ x => f (σ_d.symm x)) (σ_d x)
  rcases HA with ⟨a', ha'1, ha'2⟩
  use λ x => a' (σ_d x)
  constructor
  · -- 1.
    simp only ; clear ha'2
    constructor
    · -- 1.
      unfold conjugate ; clear H
      rw [Set.mem_setOf_eq]
      use a'
      refine ⟨ ha'1.1, ?_ ⟩
      ext y
      simp only [Function.comp_apply]
      done
    · -- 2.
      rintro y' hy' ; clear H 
      have := ha'1.2 (σ_d y') 
      simp at this
      apply this ; clear this
      exact hy'
      done
    done
  · -- 2.
    simp only [and_imp] ; clear ha'1
    rintro a1 ha1 ha1f
    unfold conjugate at ha1
    rw [Set.mem_setOf_eq] at ha1
    rcases ha1 with ⟨a2, ha2, rfl⟩ ; clear H
    have : a2 = a' := by
      apply ha'2 ; clear ha'2 a'
      refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
      rintro y' hy'
      specialize ha1f (σ_d.symm y') (by contrapose! hy' ; rw [hy', Equiv.apply_symm_apply])
      rw [← ha1f]
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      done
    rw [this]
    ext
    simp only [Function.comp_apply]
    done
  done

theorem conjugate.main {n d : Nat} {H : 𝓗 n d} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) :
  A ∈ H.set ↔ conjugate σ_d A ∈ H.set := by
  constructor
  · -- 1.
    exact conjugate.main_imp σ_d A
    done
  · -- 2.
    rintro HA'
    have HA'' := @conjugate.main_imp n d H σ_d.symm (conjugate σ_d A) HA' ; clear HA'
    have : conjugate σ_d.symm (conjugate σ_d A) = A := by
      unfold conjugate
      ext f
      simp
      constructor
      · -- 1.
        rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
        simp only [comp_equiv_symm]
        exact hf
      · -- 2.
        rintro hf
        use λ x => f (σ_d x)
        constructor
        · exact ⟨ f, hf, rfl ⟩
        · ext x ; simp only [Function.comp_apply, Equiv.apply_symm_apply]
      done
    rw [← this]
    exact HA''
    done

lemma Blindconjugate.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (Blindconjugate σ_d A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1
  · -- 1.
    simp only [H0, if_true] ; clear H0
    intro HA f x
    specialize HA (λ x => f (σ_d.symm x)) (σ_d x)
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => a' (σ_d x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        unfold Blindconjugate
        rw [Set.mem_setOf_eq]
        exact ⟨ a', ha'1.1, by ext y ; rw [Function.comp_apply] ⟩
      · -- 2.
        rintro y' hy'
        have := ha'1.2 (σ_d y') 
        rw [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply] at this
        exact this hy'
    · -- 2.
      simp only [and_imp] ; clear ha'1
      rintro a1 ha1 ha1f
      unfold Blindconjugate at ha1
      rw [Set.mem_setOf_eq] at ha1
      rcases ha1 with ⟨a2, ha2, rfl⟩
      unfold Function.comp
      have : a2 = a' := by
        apply ha'2 ; clear ha'2 a'
        refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
        rintro y' hy'
        specialize ha1f (σ_d.symm y') (by contrapose! hy' ; rw [hy', Equiv.apply_symm_apply])
        rw [← ha1f, Function.comp_apply, Equiv.apply_symm_apply]
        done
      rw [this]
    done
  ·
    simp only [H0, if_false]
  done

theorem Blindconjugate.main {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A ↔ is_LatinHypercube (Blindconjugate σ_d A) := by
  intro A
  constructor
  · -- 1.
    exact Blindconjugate.main_imp σ_d A
    done
  · -- 2.
    rintro HA
    have HA' := @Blindconjugate.main_imp n d σ_d.symm (Blindconjugate σ_d A) HA ; clear HA
    have : Blindconjugate σ_d.symm (Blindconjugate σ_d A) = A := by
      unfold Blindconjugate
      ext f
      simp
      constructor
      · -- 1.
        rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
        have : (f ∘ σ_d) ∘ σ_d.symm = f := by
          ext x
          rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
          done
        rw [this]
        exact hf
      · -- 2.
        rintro hf
        use λ x => f (σ_d x)
        constructor
        · exact ⟨ f, hf, rfl ⟩
        · ext x ; simp only [Function.comp_apply, Equiv.apply_symm_apply]
      done
    rw [← this]
    exact HA'
    done

-- Define Conjugation class
class Conjugation (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (σ_d : Fin d ≃ Fin d)
  (conj : toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = a ∘ σ_d}, conjugate.main_imp σ_d A.set A.prop ⟩)
  (inv_conj : toEquiv.invFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = a ∘ σ_d.symm}, 
      conjugate.main_imp σ_d.symm A.set A.prop ⟩)

class Paratopism {n d : Nat} (H : 𝓗 n d) extends LHCT H where
  (σ_d : Fin d ≃ Fin d)
  (σₙd : Fin d → Fin n ≃ Fin n)
  (Para : to_fun = λ (A : Set (Fin d → Fin n)) => {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => (σₙd (σ_d x)) ((a ∘ σ_d) x))})


instance : Group (Isotopism H) where
  one := ⟨ λ A => Equiv., λ A HA => HA, λ A => A, λ A HA => HA, 
          λ A => by simp only [Function.left_id, Function.right_id], 
          λ A => by simp only [Function.left_id, Function.right_id] ⟩
  mul := Mul.mul
  inv := Inv.inv
  mul_assoc := by
    intros a b c
    ext A
    simp only [Mul.mul, Function.comp_apply]
    done
  one_mul := by
    intro a
    ext A
    simp only [Mul.mul, Function.comp_apply]
    done
  mul_one := by
    intro a
    ext A
    simp only [Mul.mul, Function.comp_apply]
    done
  mul_left_inv := by
    intro a
    ext A
    simp only [Mul.mul, Inv.inv, Function.comp_apply]
    done
  

/-
"The stabilisers of a latin hypercube L under isotopism, paratopism and isomorphism
are known respectively as the autotopism group, autoparatopism group and automorphism
group of L. We use respectively Is(L), Par(L) and Aut(L) to denote these groups. For
example, Aut(L) = {σ ∈ ∆d+1n | Lσ = L}."
-/


def single_isotopism {n d : Nat} (σₙ : Fin n ≃ Fin n) (y : Fin d) (A : Set (Fin d → Fin n)) :
  Set (Fin d → Fin n) := 
  {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => if x = y then σₙ (a y) else (a x))}

def isotopism.inverse_map {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) :=
  isotopism (λ x => (σₙd x).symm) A

def isomorphism {n d : Nat} (σₙ : Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) :=
  {b : Fin d → Fin n | ∃ a ∈ A, b = σₙ ∘ a}

def conjugate.inverse_map {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) :=
  conjugate σ_d.symm A

def paratopism {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := conjugate σ_d (isotopism σₙd A)

def paratopism.raw {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => (σₙd (σ_d x)) ((a ∘ σ_d) x))}

def paratopism.inverse_map {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := isotopism.inverse_map σₙd (conjugate.inverse_map σ_d A)

def paratopism.inverse_map_raw {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => (σₙd x).symm ((a ∘ σ_d.symm) x))}




structure Isotopism {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :=
  (to_fun : Set (Fin d → Fin n) → Set (Fin d → Fin n))
  (prop : to_fun = λ A => {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => σₙd x (a x))})




structure conjugate_equiv {n d : Nat} (σ_d : Fin d ≃ Fin d) :=
  (to_fun : Set (Fin d → Fin n) → Set (Fin d → Fin n))
  (inv_fun : Set (Fin d → Fin n) → Set (Fin d → Fin n))
  (fun_def : to_fun = conjugate σ_d)
  (inv_def : inv_fun = conjugate σ_d.symm)
  (left_inv : Function.LeftInverse inv_fun to_fun)
  (right_inv : Function.RightInverse inv_fun to_fun)

structure paratopism_equiv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :=
  (to_fun : Set (Fin d → Fin n) → Set (Fin d → Fin n))
  (inv_fun : Set (Fin d → Fin n) → Set (Fin d → Fin n))
  (prop : to_fun = paratopism σ_d σₙd)
  (prop_inv : inv_fun = paratopism.inverse_map σ_d σₙd)
  (left_inv : Function.LeftInverse inv_fun to_fun)
  (right_inv : Function.RightInverse inv_fun to_fun)

-- composite defintion of paratopism and the direct definition are equivalent
lemma paratopism.raw.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), paratopism.raw σ_d σₙd A = paratopism σ_d σₙd A := by
  intro A
  ext f
  simp [paratopism.raw, paratopism, conjugate, isotopism, Function.comp_apply]
  constructor
  · -- 1.
    rintro ⟨a, ha, rfl⟩
    use λ x => (σₙd x) (a x)
    refine ⟨ ?_, by ext x; rw [Function.comp_apply] ⟩
    exact ⟨ a, ha, rfl ⟩
  · -- 2.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    exact ⟨ a, ha, by ext x; rw [Function.comp_apply] ⟩
  done

-- composite definition of paratopism.inverse_map and the direct definition are equivalent
lemma paratopism.inverse_map_raw.main {n d : Nat} (σ_d : Fin d ≃ Fin d) 
  (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), paratopism.inverse_map_raw σ_d σₙd A = 
    paratopism.inverse_map σ_d σₙd A := by
  intro A
  ext f
  simp [paratopism.inverse_map_raw, paratopism.inverse_map, conjugate.inverse_map, 
        isotopism.inverse_map, Function.comp_apply, isotopism, conjugate]
  constructor
  · -- 1.
    rintro ⟨a, ha, rfl⟩
    use λ x => a (σ_d.symm x)
    refine ⟨ ?_, rfl ⟩
    exact ⟨ a, ha, by ext x; rw [Function.comp_apply] ⟩
  · -- 2.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    exact ⟨ a, ha, by ext x; rw [Function.comp_apply] ⟩
  done


-- isomorphism and single_isotopism are the just a specific case of isotopism
lemma isomorphism.isotopism {n d : Nat} (σₙ : Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  isomorphism σₙ A = isotopism (λ _ => σₙ) A := by
  unfold isomorphism isotopism
  ext f
  constructor <;>
  · -- both cases needs exactly the same proof
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro a ha rfl
    refine ⟨ a, ha, ?_ ⟩ ; clear ha
    ext x
    simp only [Function.comp_apply]
    done

lemma single_isotopism.isotopism {n d : Nat} (σₙ : Fin n ≃ Fin n) (y : Fin d) 
    (A : Set (Fin d → Fin n)) :
  single_isotopism σₙ y A = isotopism (λ x => if x =y then σₙ else Equiv.refl (Fin n)) A := by
  unfold single_isotopism isotopism
  ext f
  constructor <;>
  · -- both cases needs exactly the same proof
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro a ha rfl
    refine ⟨ a, ha, ?_ ⟩ ; clear ha
    ext x
    by_cases h : x = y <;>
    simp only [h, Function.comp_apply, if_true, if_false, Equiv.refl_apply]
    done



-- small lemmas
@[simp]
lemma comp_equiv_symm {α β γ : Type _} (f : β → γ) (σ : α ≃ β) : (f ∘ σ) ∘ σ.symm = f := by
  ext x
  rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
  done

@[simp]
lemma comp_symm_equiv {α β γ : Type _} (f : α → γ) (σ : α ≃ β) : (f ∘ σ.symm) ∘ σ = f := by
  ext x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  done

-- Isotopism is an equivalence relation
lemma isotopism.left_inverse {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (isotopism.inverse_map σₙd) (isotopism σₙd) := by
  unfold isotopism inverse_map Function.LeftInverse
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact hf
    done
  · -- 2.
    rintro hf
    use λ x => (σₙd x) (f x)
    simp only [Equiv.symm_apply_apply, and_true]
    exact ⟨ f, hf, rfl ⟩
    done

lemma isotopism.right_inverse {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (isotopism.inverse_map σₙd) (isotopism σₙd) := by
  unfold isotopism inverse_map Function.RightInverse Function.LeftInverse
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply]
    exact hf
    done
  · -- 2.
    rintro hf
    use λ x => (σₙd x).symm (f x)
    simp only [Equiv.apply_symm_apply, and_true]
    exact ⟨ f, hf, rfl ⟩
    done

theorem isotopism.Equiv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Equiv (Set (Fin d → Fin n)) (Set (Fin d → Fin n)) := by
  refine ⟨ isotopism σₙd, isotopism.inverse_map σₙd, ?_, ?_ ⟩
  exact isotopism.left_inverse σₙd
  exact isotopism.right_inverse σₙd
  done

-- Conjugation is an equivalence relation
lemma conjugate.left_inverse {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.LeftInverse (@conjugate.inverse_map n d σ_d) (conjugate σ_d) := by
  unfold conjugate inverse_map Function.LeftInverse
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
    rw [comp_equiv_symm f σ_d]
    exact hf
    done
  · -- 2.
    rintro hf
    use λ x => f (σ_d x)
    constructor
    · -- 1.
      refine ⟨ f, hf, ?_ ⟩
      ext x
      rw [Function.comp_apply]
      done
    · -- 2.
      ext x
      rw [Function.comp_apply, Equiv.apply_symm_apply]
      done
  done

lemma conjugate.right_inverse {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.RightInverse (@conjugate.inverse_map n d σ_d) (conjugate σ_d) := by
  unfold conjugate inverse_map Function.RightInverse Function.LeftInverse
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
    rw [comp_symm_equiv f σ_d]
    exact hf
    done
  · -- 2.
    rintro hf
    use λ x => f (σ_d.symm x)
    constructor
    · -- 1.
      refine ⟨ f, hf, ?_ ⟩
      ext x
      rw [Function.comp_apply]
      done
    · -- 2.
      ext x
      rw [Function.comp_apply, Equiv.symm_apply_apply]
      done
  done

@[simp]
theorem conjugate.Equiv {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Equiv (Set (Fin d → Fin n)) (Set (Fin d → Fin n)) := by
  refine ⟨ conjugate σ_d, conjugate.inverse_map σ_d, ?_, ?_ ⟩
  exact conjugate.left_inverse σ_d
  exact conjugate.right_inverse σ_d
  done

-- Paratopism is an equivalence relation
lemma paratopism.left_inverse {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (paratopism.inverse_map σ_d σₙd) (paratopism σ_d σₙd) := by
  unfold paratopism inverse_map Function.LeftInverse isotopism 
  unfold conjugate isotopism.inverse_map conjugate.inverse_map
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨ _, ⟨ _, ⟨ _, ⟨ a, H, rfl ⟩, rfl ⟩, rfl ⟩, rfl ⟩
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact H
  · -- 2.
    rintro H
    exact ⟨ λ x => (σₙd x) (f x), 
            ⟨ λ x => (σₙd (σ_d x)) (f (σ_d x)), 
              ⟨ λ x => (σₙd x) (f x), 
                ⟨ f, H, rfl ⟩, 
                rfl 
              ⟩, 
              (by ext x ; simp) 
            ⟩, 
            (by ext x ; simp) 
          ⟩
    done
  done

lemma paratopism.right_inverse {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (paratopism.inverse_map σ_d σₙd) (paratopism σ_d σₙd) := by
  unfold paratopism inverse_map Function.RightInverse Function.LeftInverse
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨ _, ⟨ _, ⟨ _, ⟨ a, H, rfl ⟩, rfl ⟩, rfl ⟩, rfl ⟩
    simp
    have : (fun x => a (σ_d.symm x)) ∘ ↑σ_d = a := by
      ext y
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      done
    rw [this]
    exact H
    done
  · -- 2.
    rintro H
    exact ⟨ λ x => f (σ_d.symm x),
            ⟨ λ x => (σₙd x).symm (f (σ_d.symm x)),
              ⟨ λ x => (f (σ_d.symm x)),
                ⟨ f, H, rfl ⟩,
                rfl
              ⟩, 
              (by ext x ; simp)
            ⟩, 
            (by ext x ; simp)
          ⟩
    done

@[simp]
theorem paratopism.Equiv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Equiv (Set (Fin d → Fin n)) (Set (Fin d → Fin n)) := by
  refine ⟨ paratopism σ_d σₙd, paratopism.inverse_map σ_d σₙd, ?_, ?_ ⟩
  exact paratopism.left_inverse σ_d σₙd
  exact paratopism.right_inverse σ_d σₙd
  done


-- Isotopism, conjugation and paratopism each are closed under composition
lemma isotopism.comp {n d : Nat} {σₙd1 σₙd2 : Fin d → Fin n ≃ Fin n} {A : Set (Fin d → Fin n)} :
  True := by
  rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  use λ x => (σₙd x) (a (b x))
  
  constructor
  · -- 1.
    refine ⟨ a (b x), ?_, ?_ ⟩
    exact ⟨ a, ha, rfl ⟩
    exact ⟨ b, hb, rfl ⟩
    done
  · -- 2.
    ext x
    simp only [Function.comp_apply]
    done
  done

-- Isotopism, conjugation and paratopism preserve the property of being a latin hypercube

-- Proof Strategy :
-- f                         Profit!
-- |                           ↑
--undo permunation         permutation
-- ↓                           |
-- f'  -Find the point in A →  a'


theorem single_isotopism.main {n d : Nat} {H : 𝓗 n d} (σₙ : Fin n ≃ Fin n) (y : Fin d) 
  (A : Set (Fin d → Fin n)) :
  A ∈ H.set ↔ single_isotopism σₙ y A ∈ H.set := by 
  rw [single_isotopism.isotopism σₙ y A, ← isotopism.main]

theorem isomorphism.main {n d : Nat} {H : 𝓗 n d} (σₙ : Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  A ∈ H.set ↔ isomorphism σₙ A ∈ H.set := by rw [isomorphism.isotopism σₙ A, ← isotopism.main]


lemma paratopism.main_imp {n d : Nat} {H : 𝓗 n d} (σ_d : Fin d ≃ Fin d) 
  (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  A ∈ H.set → paratopism σ_d σₙd A ∈ H.set := by
  unfold paratopism
  rintro HA
  apply conjugate.main_imp σ_d (isotopism σₙd A)
  apply isotopism.main_imp σₙd A
  exact HA
  done

theorem paratopism.main {n d : Nat} {H : 𝓗 n d} (σ_d : Fin d ≃ Fin d) 
  (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  A ∈ H.set ↔ paratopism σ_d σₙd A ∈ H.set := by
  constructor
  · -- 1.
    exact paratopism.main_imp σ_d σₙd A
    done
  · -- 2.
    unfold paratopism
    rintro HA
    rw [← isotopism.left_inverse σₙd A]
    apply isotopism.main_imp (λ x => (σₙd x).symm) (isotopism σₙd A)
    rw [← conjugate.left_inverse σ_d (isotopism σₙd A)]
    apply conjugate.main_imp σ_d.symm (conjugate σ_d (isotopism σₙd A)) 
    exact HA


-- Quotienting by the equivalence relation

def isotopism.relation {n d : Nat} : Set (Fin d → Fin n) → 
  Set (Fin d → Fin n) → Prop := 
  λ A B => ∃ σₙd : Fin d → Fin n ≃ Fin n, isotopism σₙd A = B

lemma isotopism.relation.refl {n d : Nat} : Reflexive (@isotopism.relation n d) := by
  rintro A
  use λ _ => Equiv.refl (Fin n)
  simp only [isotopism, Equiv.refl_apply, exists_eq_right', Set.setOf_mem_eq]
  done

lemma isotopism.relation.symm {n d : Nat} : ∀ {x y : Set (Fin d → Fin n)}, 
  isotopism.relation x y → isotopism.relation y x  := by
  rintro A B ⟨σₙd, rfl⟩
  use λ x => (σₙd x).symm
  apply isotopism.left_inverse
  done

lemma isotopism.relation.trans {n d : Nat} : ∀ {x y z : Set (Fin d → Fin n)}, 
  isotopism.relation x y → isotopism.relation y z → isotopism.relation x z := by
  rintro A B C ⟨σₙd, rfl⟩ ⟨τₙd, rfl⟩
  use λ x => Equiv.trans (σₙd x) (τₙd x)
  ext f
  constructor <;> 
  simp only [isotopism, Equiv.trans_apply, Set.mem_setOf_eq, forall_exists_index, and_imp]
  · -- 1.
    rintro a1 ha1 rfl
    use fun x => (σₙd x) (a1 x)
    exact ⟨ ⟨ a1, ha1, rfl ⟩, rfl ⟩
  · -- 2.
    rintro _ a ha rfl rfl
    refine ⟨ a, ha, rfl ⟩
    done
  done

def isotopism.relation.setoid {n d : Nat} : Setoid (Set (Fin d → Fin n)) :=
⟨ 
  isotopism.relation, 
  ⟨ isotopism.relation.refl, isotopism.relation.symm, isotopism.relation.trans ⟩
⟩

def isotopism.class (n d : Nat) := 
  Quotient (isotopism.relation.setoid : Setoid (Set (Fin d → Fin n)))


def conjugate.relation {n d : Nat} : Set (Fin d → Fin n) → 
  Set (Fin d → Fin n) → Prop := 
  λ A B => ∃ σ_d : Fin d ≃ Fin d, conjugate σ_d A = B

lemma conjugate.relation.refl {n d : Nat} : Reflexive (@conjugate.relation n d) := by
  rintro A
  use Equiv.refl (Fin d)
  simp only [conjugate, Equiv.coe_refl, Function.comp.right_id, exists_eq_right', Set.setOf_mem_eq]
  done

lemma conjugate.relation.symm {n d : Nat} : ∀ {x y : Set (Fin d → Fin n)}, 
  conjugate.relation x y → conjugate.relation y x  := by
  rintro A B ⟨σ_d, rfl⟩
  use σ_d.symm
  apply conjugate.left_inverse
  done

lemma conjugate.relation.trans {n d : Nat} : ∀ {x y z : Set (Fin d → Fin n)},
  conjugate.relation x y → conjugate.relation y z → conjugate.relation x z := by
  rintro A B C ⟨σ_d, rfl⟩ ⟨τ_d, rfl⟩
  use Equiv.trans τ_d σ_d 
  ext f
  constructor <;>
  simp
  · -- 1.
    rintro ⟨ a, ha, rfl ⟩
    use a ∘ σ_d
    constructor
    · exact ⟨ a, ha, rfl ⟩
    · ext x ; simp
  · -- 2.
    rintro ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩
    exact ⟨ a, ha, rfl ⟩
  done

def conjugate.relation.setoid {n d : Nat} : Setoid (Set (Fin d → Fin n)) :=
⟨ 
  conjugate.relation,
  ⟨ conjugate.relation.refl, conjugate.relation.symm, conjugate.relation.trans ⟩
⟩

def conjugate.class (n d : Nat) := 
  Quotient (conjugate.relation.setoid : Setoid (Set (Fin d → Fin n)))


def paratopism.relation {n d : Nat} : Set (Fin d → Fin n) →
  Set (Fin d → Fin n) → Prop := 
  λ A B => ∃ σ_d : Fin d ≃ Fin d, ∃ σₙd : Fin d → Fin n ≃ Fin n, 
    paratopism σ_d σₙd A = B
  
lemma paratopism.relation.refl {n d : Nat} : Reflexive (@paratopism.relation n d) := by
  rintro A
  use Equiv.refl (Fin d)
  use λ _ => Equiv.refl (Fin n)
  simp only [paratopism, conjugate, isotopism, Equiv.refl_apply, exists_eq_right', Set.setOf_mem_eq, Equiv.coe_refl,
    Function.comp.right_id]
  done

lemma paratopism.relation.symm {n d : Nat} : ∀ {x y : Set (Fin d → Fin n)},
  paratopism.relation x y → paratopism.relation y x  := by
  rintro A B ⟨σ_d, ⟨σₙd, rfl⟩⟩
  use σ_d
  use λ x => (σₙd (σ_d x))
  nth_rw 2 [← paratopism.left_inverse σ_d σₙd A]
  ext f
  constructor <;>
  simp only [paratopism, conjugate, isotopism, Set.mem_setOf_eq, inverse_map, isotopism.inverse_map,
    conjugate.inverse_map, forall_exists_index, and_imp]
  · -- 1.
    rintro a1 a2 a3 a4 ha4 ha3 ha2 rfl hf 
    use fun x => (σₙd x) (f x)
    refine ⟨ ?_, by simp ⟩
    use fun x => (σₙd (σ_d x)) (f (σ_d x))
    refine ⟨ ?_, by ext x; simp ⟩
    use fun x => (σₙd x) (f x)
    refine ⟨ ?_, by ext x; simp ⟩
    use a4
    refine ⟨ ha4, ?_ ⟩
    

    rintro _ _ _ a hx rfl rfl rfl rfl
    use a
    constructor
    · -- 1.
      refine ⟨ a ∘ ↑σ_d, ?_, by simp ⟩
      refine ⟨ a, ?_, rfl ⟩
      
      done
    · -- 2.
      simp
      
      done
    done
  done

