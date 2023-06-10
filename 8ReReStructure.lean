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

  
def isotopism {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : LatinHypercube n d) :
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

def isotopism.inverse_map {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : LatinHypercube n d) :
  LatinHypercube n d := ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => (σₙd x).symm (a x))}, by
    have := A.prop
    revert this
    unfold is_LatinHypercube
    simp only [gt_iff_lt, A.H0, and_self, ne_eq, dite_eq_ite, ite_true]

    rintro HA f x
    specialize HA (λ x => (σₙd x) (f x)) x
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => (σₙd x).symm (a' x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy'
        rw [ha'1.2 y' hy', Equiv.symm_apply_apply]
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
        rw [← (ha1f y' hy'), Equiv.apply_symm_apply]
        done
      rw [this]
    done
    ⟩

def single_isotopism {n d : Nat} (σₙ : Fin n ≃ Fin n) (y : Fin d) (A : LatinHypercube n d) :
  LatinHypercube n d := isotopism (λ x => if x = y then σₙ else Equiv.refl (Fin n)) A

def isomorphism {n d : Nat} (σₙ : Fin n ≃ Fin n) (A : LatinHypercube n d) : 
  LatinHypercube n d := isotopism (λ _ => σₙ) A

def conjugate {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : LatinHypercube n d) : 
  LatinHypercube n d := ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = a ∘ σ_d}, by
    have := A.prop
    revert this
    unfold is_LatinHypercube
    simp only [gt_iff_lt, A.H0, and_self, ne_eq, dite_eq_ite, ite_true]

    rintro HA f x
    specialize HA (λ x => f (σ_d.symm x)) (σ_d x)
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => a' (σ_d x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy'
        have := ha'1.2 (σ_d y') 
        rw [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply] at this
        exact this hy'
      done
    · -- 2.
      simp only [and_imp] ; clear ha'1
      rintro a1 ha1 ha1f
      rcases ha1 with ⟨a2, ha2, rfl⟩
      have : a2 = a' := by
        apply ha'2 ; clear ha'2 a'
        refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
        rintro y' hy'
        specialize ha1f (σ_d.symm y') (by contrapose! hy' ; rw [hy', Equiv.apply_symm_apply])
        rw [← ha1f, Function.comp_apply, Equiv.apply_symm_apply]
        done
      rw [this]
      rfl
    done
  ⟩

def conjugate.inverse_map {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : LatinHypercube n d) : 
  LatinHypercube n d := ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => a (σ_d.symm x))}, by
    have := A.prop
    revert this
    unfold is_LatinHypercube
    simp only [gt_iff_lt, A.H0, and_self, ne_eq, dite_eq_ite, ite_true]

    rintro HA f x
    specialize HA (λ x => f (σ_d x)) (σ_d.symm x)
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => a' (σ_d.symm x)
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy'
        have := ha'1.2 (σ_d.symm y') 
        rw [EmbeddingLike.apply_eq_iff_eq, Equiv.apply_symm_apply] at this
        exact this hy'
      done
    · -- 2.
      simp only [and_imp] ; clear ha'1
      rintro a1 ha1 ha1f
      rcases ha1 with ⟨a2, ha2, rfl⟩
      have : a2 = a' := by
        apply ha'2 ; clear ha'2 a'
        refine ⟨ ha2, ?_ ⟩ ; clear ha2 A
        rintro y' hy'
        specialize ha1f (σ_d y') (by contrapose! hy' ; rw [hy', Equiv.symm_apply_apply])
        rw [← ha1f]
        simp only [Equiv.symm_apply_apply]
        done
      rw [this]
    done
  ⟩

def paratopism {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : LatinHypercube n d) : 
  LatinHypercube n d := conjugate σ_d (isotopism σₙd A)

def paratopism.inverse_map {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : LatinHypercube n d) : 
  LatinHypercube n d := isotopism.inverse_map σₙd (conjugate.inverse_map σ_d A)

theorem isotopism.toEquiv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : LatinHypercube n d) :
  Equiv (LatinHypercube n d) (LatinHypercube n d) := by
  refine ⟨ isotopism σₙd, isotopism.inverse_map σₙd, ?_, ?_ ⟩
  · 
    intro A'
    simp only [inverse_map, isotopism, Set.mem_setOf_eq]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Equiv.symm_apply_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => (σₙd x) (f x)
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Equiv.symm_apply_apply]
      done
  · 
    intro A'
    simp only [inverse_map, isotopism, Set.mem_setOf_eq]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Equiv.apply_symm_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => (σₙd x).symm (f x)
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Equiv.apply_symm_apply]
  done

theorem conjugate.toEquiv {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : LatinHypercube n d) :
  Equiv (LatinHypercube n d) (LatinHypercube n d) := by
  refine ⟨ conjugate σ_d, conjugate.inverse_map σ_d, ?_, ?_ ⟩
  · 
    intro A'
    simp only [inverse_map, conjugate, Set.mem_setOf_eq, Function.comp]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => f (σ_d x)
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      done
  · 
    intro A'
    simp only [inverse_map, conjugate, Set.mem_setOf_eq, Function.comp]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Equiv.symm_apply_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => f (σ_d.symm x)
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Equiv.symm_apply_apply]
  done

theorem paratopism.toEquiv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : LatinHypercube n d) :
  Equiv (LatinHypercube n d) (LatinHypercube n d) := by
  refine ⟨ paratopism σ_d σₙd, paratopism.inverse_map σ_d σₙd, ?_, ?_ ⟩
  · 
    intro A'
    simp only [inverse_map, paratopism, conjugate, conjugate.inverse_map, isotopism, isotopism.inverse_map, Set.mem_setOf_eq, Function.comp]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => (σₙd x) (f (σ_d.symm x))
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      done
  · 
    intro A'
    simp only [inverse_map, paratopism, Set.mem_setOf_eq, Function.comp]
    congr
    ext f
    constructor
    · -- 1.
      rintro ⟨a, ⟨ a', ha', rfl ⟩, rfl⟩
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      exact ha'
    · -- 2.
      rintro ha'
      use λ x => (σₙd x).symm (f (σ_d x))
      constructor
      · -- 1.
        exact ⟨ f, ha', rfl ⟩
      · -- 2.
        simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      done
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
