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


-- Define Different types of transformations on latin hypercubes

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


-- These transformations are all bijections on the set of latin hypercubes

theorem isotopism.toEquiv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
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

theorem conjugate.toEquiv {n d : Nat} (σ_d : Fin d ≃ Fin d) :
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

theorem paratopism.toEquiv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Equiv (LatinHypercube n d) (LatinHypercube n d) := by
  refine ⟨ paratopism σ_d σₙd, paratopism.inverse_map σ_d σₙd, ?_, ?_ ⟩ <;>
  intro A' <;>
  unfold inverse_map paratopism conjugate conjugate.inverse_map isotopism isotopism.inverse_map <;>
  simp only [Set.mem_setOf_eq, Function.comp] <;>
  congr <;>
  ext f <;>
  constructor
  · -- 1.
    rintro ⟨_, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact ha
  · -- 2.
    rintro ha'
    use fun x => (σₙd x) (f x)
    constructor
    · -- 1.
      refine ⟨ λ x => (σₙd (σ_d x)) (f (σ_d x)), ?_, by simp only [Equiv.apply_symm_apply] ⟩
      refine ⟨ fun x => (σₙd x) (f x), ?_, rfl ⟩
      refine ⟨ f, ha', rfl ⟩
    · -- 2.
      simp only [Equiv.symm_apply_apply]
    done
  · -- 1.
    rintro ⟨_, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact ha
  · -- 2.
    rintro ha'
    use fun x => f (σ_d.symm x)
    constructor
    · -- 1.
      refine ⟨ fun x => (σₙd x).symm ((fun x => f (σ_d.symm x)) x), ?_, by simp only [Equiv.apply_symm_apply] ⟩
      refine ⟨ fun x => f (σ_d.symm x), ?_, by rfl ⟩
      refine ⟨ f, ha', rfl ⟩
    · -- 2.
      simp only [Equiv.symm_apply_apply]
    done
  done


-- With composition as multiplication, these transformations form a group
structure Isotopism (n d : Nat) :=
  (H0 : n > 0 ∧ d > 1)
  (toFun : LatinHypercube n d → LatinHypercube n d)
  (iso : ∃ σₙd : Fin d → Fin n ≃ Fin n, toFun = isotopism σₙd)


@[ext]
theorem Isotopism.ext {n d : Nat} (T1 T2 : Isotopism n d) :
  T1.toFun = T2.toFun → T1 = T2 := by
  intro h
  cases T1 ; cases T2
  congr
  done

def Isotopism.mul {n d : Nat} : Isotopism n d → Isotopism n d → Isotopism n d :=
 λ T1 T2 : Isotopism n d => ⟨ 
  T1.H0, fun x => toFun T1 (toFun T2 x), by
    rcases T1.iso with ⟨σₙd1, h1⟩
    rcases T2.iso with ⟨σₙd2, h2⟩
    use fun x => (σₙd2 x).trans (σₙd1 x)
    ext A
    rw [h1, h2]
    unfold isotopism
    congr
    ext a
    simp only [Set.mem_setOf_eq, Equiv.trans_apply]
    constructor
    · -- 1.
      rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨ a, ha, rfl⟩
    · -- 2.
      rintro ⟨a, ha, rfl⟩
      exact ⟨ _, ⟨a, ha, rfl⟩, rfl⟩
      done
  ⟩

def Isotopism.one {n d : Nat} (H0 : n > 0 ∧ d > 1) : Isotopism n d := 
⟨ 
  H0, id, by
    use fun _ => Equiv.refl (Fin n)
    unfold isotopism
    congr
    simp only [Equiv.refl_apply, exists_eq_right', Set.setOf_mem_eq]
⟩

noncomputable def Isotopism.inv {n d : Nat} : Isotopism n d → Isotopism n d := 
  λ T : Isotopism n d => by
    choose σₙd _ using T.iso
    exact ⟨ T.H0, isotopism (fun x => (σₙd x).symm), ⟨ fun x => (σₙd x).symm, rfl ⟩  ⟩


theorem Isotopism.inv_leftinv {n d : Nat} (T : Isotopism n d) : Function.LeftInverse (Isotopism.inv T).toFun T.toFun := by
  rintro x
  rcases T.iso with ⟨σₙd1, h1⟩
  rw [h1] ; clear h1
  unfold inv
  simp
  have this := Classical.choose_spec T.inv.iso
  unfold isotopism
  congr
  simp
  ext a
  constructor
  · -- 1.
    rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simp
    
    done
  · -- 2.
    sorry
    done
  -- rcases T.inv.iso with ⟨σₙd2, h2⟩
  -- rw [h1, h2] ; clear h1 h2


-- instance group : Group (AddAut A) := by
--   refine'
--   { mul := fun g h => AddEquiv.trans h g
--     one := AddEquiv.refl A
--     inv := AddEquiv.symm
--     div := fun g h => AddEquiv.trans h.symm g
--     npow := @npowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩
--     zpow := @zpowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩ ⟨AddEquiv.symm⟩
--     .. } <;>
--   intros <;>
--   ext <;>
--   try rfl
--   apply Equiv.left_inv


noncomputable instance Isotopism.Group {n d : Nat} (H0 : n > 0 ∧ d > 1) : Group (Isotopism n d) := by
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

