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

  by_cases H0 : n > 0 ∧ d > 1 <;> simp only [H0, if_true, if_false] ; clear H0
  · -- 1.
    rintro HA f x
    specialize HA (λ x => (σₙd x).symm (f x)) x
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => σₙd x (a' x)
    constructor <;> simp only [Blindisotopism, and_imp]
    · -- 1.
      refine ⟨ ⟨ a', ha'1.1, rfl ⟩, ?_ ⟩ ; clear ha'2
      rintro y' hy'
      rw [ha'1.2 y' hy', Equiv.apply_symm_apply]
      done
    · -- 2.
      rintro _ ⟨a2, ha2, rfl⟩ ha1f ; clear ha'1
      suffices h : a2 = a' by rw [h]
      apply ha'2 _ ⟨ ha2, ?_ ⟩ ; clear ha'2 a' ha2 A
      rintro y' hy'
      rw [← (ha1f y' hy'), Equiv.symm_apply_apply]
  done

theorem Blindisotopism.main {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (Blindisotopism σₙd A) := by
  refine ⟨ Blindisotopism.main_imp σₙd A, ?_ ⟩
  rintro HA
  have HA' := Blindisotopism.main_imp (λ x => (σₙd x).symm) (Blindisotopism σₙd A) HA ; clear HA
  suffices H : Blindisotopism (fun x => (σₙd x).symm) (Blindisotopism σₙd A) = A by rw [← H] ; exact HA'
  ext f ; clear HA'
  constructor
  · -- 1.
    rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact hf
  · -- 2.
    rintro hf
    refine ⟨ λ x => (σₙd x) (f x), ⟨ f, hf, rfl ⟩, ?_ ⟩
    simp only [Equiv.symm_apply_apply]
  done
  

lemma Blindisotopism.closed_under_comp {n d : Nat} (σₙd1 σₙd2 : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n) ) :
  Blindisotopism σₙd1 (Blindisotopism σₙd2 A) = Blindisotopism (λ x => Equiv.trans (σₙd2 x) (σₙd1 x)) A := by
  unfold Blindisotopism Equiv.trans
  simp only [Set.mem_setOf_eq, Equiv.coe_fn_mk]
  ext
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    exact ⟨ a, ha, rfl ⟩
  · -- 2.
    rintro ⟨a, ha, rfl⟩
    exact ⟨ λ x => (σₙd2 x) (a x), ⟨ a, ha, rfl ⟩, rfl ⟩
  done

lemma Blindisotopism.closed_under_inv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (Blindisotopism σₙd) (Blindisotopism (λ x => (σₙd x).symm)) := by
  unfold Blindisotopism Equiv.symm Function.RightInverse Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact ha
  · -- 2.
    rintro ha
    use λ x => (σₙd x) (f x)
    refine ⟨ ⟨ f, ha, rfl ⟩, by simp only [Equiv.symm_apply_apply] ⟩
  done

lemma Blindisotopism.closed_under_inv1 {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (Blindisotopism σₙd) (Blindisotopism (λ x => (σₙd x).symm)) := by
  unfold Blindisotopism Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply]
    exact ha
  · -- 2.
    rintro ha
    use λ x => (σₙd x).symm (f x)
    refine ⟨ ⟨ f, ha, rfl ⟩, by simp only [Equiv.apply_symm_apply] ⟩
  done

class Isotopism (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (iso : ∃ σₙd : Fin d → Fin n ≃ Fin n, toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, Blindisotopism σₙd A.set, Blindisotopism.main_imp σₙd A.set A.prop ⟩)

@[ext] 
theorem Isotopism.ext {n d : Nat} (T1 T2 : Isotopism n d) : 
  T1.toFun = T2.toFun → T1 = T2 := by
  intro h
  have Isotopism.ext_equiv : T1.toEquiv = T2.toEquiv → T1 = T2 := by
    rcases T1 with ⟨ ⟨ f, f1, tofunf, invfunf ⟩, iso₁ ⟩
    rcases T2 with ⟨ ⟨ g, g1, tofung, invfung ⟩, iso₂ ⟩ 
    simp only [Equiv.mk.injEq, and_imp]
    rintro h1 h2
    congr
    done
  apply Isotopism.ext_equiv
  ext A
  rw [← Equiv.toFun_as_coe, ← Equiv.toFun_as_coe, h]
  

def Isotopism.id {n d : Nat} : Isotopism n d := 
  ⟨ Equiv.refl (LatinHypercube n d), by use λ _ => Equiv.refl (Fin n); unfold Blindisotopism; simp; rfl ⟩


def Isotopism.comp { n d : Nat} (T1 T2 : Isotopism n d) : Isotopism n d := 
  ⟨ Equiv.trans T1.toEquiv T2.toEquiv,
    by 
      rcases T1 with ⟨ equiv1, ⟨ σₙd1, iso1 ⟩ ⟩
      rcases T2 with ⟨ equiv2, ⟨ σₙd2, iso2 ⟩ ⟩
      use λ x => Equiv.trans (σₙd1 x) (σₙd2 x)
      ext A
      simp only [Equiv.trans]
      rw [Equiv.toFun_as_coe] at iso1 iso2
      rw [iso1, iso2] ; clear iso1 iso2
      simp only [Function.comp_apply, LatinHypercube.mk.injEq]
      rw [Blindisotopism.closed_under_comp σₙd2 σₙd1 A.set]
      rfl
      done
  ⟩

def Isotopism.inverse_map {n d : Nat} (T : Isotopism n d) : Isotopism n d := 
  ⟨ T.toEquiv.symm, by
    rcases T with ⟨ equiv, ⟨ σₙd, iso ⟩ ⟩
    use λ x => (σₙd x).symm
    ext A  
    apply Equiv.injective equiv
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe_apply, Equiv.apply_symm_apply]
    rw [Equiv.toFun_as_coe] at iso
    rw [iso, LatinHypercube.mk.injEq]
    nth_rw 1 [← Blindisotopism.closed_under_inv1 σₙd A.set]
    done
  ⟩

theorem Isotopism.LeftInverse { n d : Nat} (T : Isotopism n d) : Isotopism.comp (Isotopism.inverse_map T) T  = Isotopism.id := by
  unfold Isotopism.comp Isotopism.inverse_map Isotopism.id Equiv.trans Function.comp
  congr <;>
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply] <;>
  rfl

instance {n d : Nat} : Group (Isotopism n d) := by
  refine'
  {
    mul := λ T1 T2 : Isotopism n d => Isotopism.comp T1 T2
    one := Isotopism.id
    inv := λ T : Isotopism n d => Isotopism.inverse_map T
    div := λ T1 T2 : Isotopism n d => Isotopism.comp T1 (Isotopism.inverse_map T2)
    npow := @npowRec _ ⟨Isotopism.id⟩ ⟨λ T1 T2 => Isotopism.comp T1 T2⟩
    zpow := @zpowRec _ ⟨Isotopism.id⟩ ⟨λ T1 T2 => Isotopism.comp T1 T2⟩ ⟨Isotopism.inverse_map⟩
    mul_left_inv := fun T => Isotopism.LeftInverse T
    .. } <;>
  intros <;>
  ext <;>
  rfl
  done

-------------------------------------------------------------------------------------------

def Blindconjugate {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = a ∘ σ_d}

lemma Blindconjugate.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (Blindconjugate σ_d A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1 <;> simp only [H0, if_true, if_false] ; clear H0
  intro HA f x 
  specialize HA (λ x => f (σ_d.symm x)) (σ_d x)
  rcases HA with ⟨a', ha'1, ha'2⟩
  use λ x => a' (σ_d x)
  simp only [and_imp, Blindconjugate]
  constructor
  · -- 1.
    refine ⟨ ⟨ a', ha'1.1, rfl ⟩, ?_ ⟩ ; clear ha'2
    rintro y' hy' 
    rw [← EmbeddingLike.apply_eq_iff_eq σ_d] at hy'
    rw [ha'1.2 (σ_d y') hy', Equiv.symm_apply_apply]
    done
  · -- 2.
    rintro _ ⟨a, ha, rfl⟩ haf ; clear ha'1
    unfold Function.comp
    suffices  h : a = a' by rw [h]
    apply ha'2 _ ⟨ ha, ?_ ⟩ ; clear ha'2 a' ha A
    rintro y' hy'
    specialize haf (σ_d.symm y') (by contrapose! hy' ; rw [hy', Equiv.apply_symm_apply])
    rw [← haf, Function.comp_apply, Equiv.apply_symm_apply]
  done

theorem Blindconjugate.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (Blindconjugate σ_d A) := by
  refine ⟨ Blindconjugate.main_imp σ_d A, ?_ ⟩
  rintro HA
  have HA' := Blindconjugate.main_imp σ_d.symm (Blindconjugate σ_d A) HA ; clear HA
  suffices H : Blindconjugate σ_d.symm (Blindconjugate σ_d A) = A by rw [← H]; exact HA'
  ext f ; clear HA'
  constructor
  · -- 1.
    rintro ⟨_, ⟨ f, hf, rfl ⟩, rfl⟩
    suffices H : (f ∘ σ_d) ∘ σ_d.symm = f by rw [H] ; exact hf
    ext
    rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    done
  · -- 2.
    rintro hf
    refine ⟨ fun x => f (σ_d x), ⟨ f, hf, rfl ⟩, ?_ ⟩
    ext
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  done

lemma Blindconjugate.closed_under_comp {n d : Nat} (σ_d1 σ_d2 : Fin d ≃ Fin d) (A : Set (Fin d → Fin n) ) :
  Blindconjugate σ_d1 (Blindconjugate σ_d2 A) = Blindconjugate (Equiv.trans σ_d1 σ_d2) A := by
  unfold Blindconjugate Equiv.trans
  simp only [Set.mem_setOf_eq, Equiv.coe_fn_mk]
  ext
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    exact ⟨ a, ha, rfl ⟩
  · -- 2.
    rintro ⟨a, ha, rfl⟩
    exact ⟨ λ x => a (σ_d2 x), ⟨ a, ha, rfl ⟩, rfl ⟩
  done
  
lemma Blindconjugate.closed_under_inv {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.RightInverse (@Blindconjugate n _ σ_d) (@Blindconjugate n _ σ_d.symm) := by
  unfold Blindconjugate Function.RightInverse Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk, Function.comp]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply]
    exact ha
  · -- 2.
    rintro ha
    exact ⟨ λ x => f (σ_d x), ⟨ f, ha, rfl ⟩, by simp only [Equiv.apply_symm_apply] ⟩
  done

--------------------------------------------------------------------------

-- Define Conjugation class
class Conjugation (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (σ_d : Fin d ≃ Fin d)
  (conj : toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = a ∘ σ_d}, Blindconjugate.main_imp σ_d A.set A.prop ⟩)
  (inv_conj : toEquiv.invFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = a ∘ σ_d.symm}, 
      Blindconjugate.main_imp σ_d.symm A.set A.prop ⟩)

def Blindparatopism {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => (σₙd (σ_d x)) ((a (σ_d x))))}

lemma Blindparatopism.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (Blindparatopism σ_d σₙd A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1
  · -- 1.
    simp only [H0, if_true] ; clear H0
    intro HA f x
    specialize HA (λ x => (σₙd x).symm (f (σ_d.symm x))) (σ_d x)
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => (σₙd (σ_d x)) (a' (σ_d x))
    unfold Blindparatopism
    constructor
    · -- 1.
      simp only ; clear ha'2
      constructor
      · -- 1.
        rw [Set.mem_setOf_eq]
        exact ⟨ a', ha'1.1, rfl ⟩
      · -- 2.
        rintro y' hy' 
        rw [ha'1.2 (σ_d y'), Equiv.symm_apply_apply, Equiv.apply_symm_apply]
        rw [EmbeddingLike.apply_eq_iff_eq]
        exact hy'
      done
    · -- 2.
      simp only [and_imp, Set.mem_setOf_eq] ; clear ha'1
      rintro _ ⟨a, ha, rfl⟩ haf
      have : a = a' := by
        apply ha'2 ; clear ha'2 a'
        refine ⟨ ha, ?_ ⟩ ; clear ha A
        rintro y' hy'
        specialize haf (σ_d.symm y') (by contrapose! hy' ; rw [hy', Equiv.apply_symm_apply])
        rw [← haf]
        simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        done
      rw [this]
    done
  · -- 2.
    simp only [H0, if_false]
  done

theorem Blindparatopism.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A ↔ is_LatinHypercube (Blindparatopism σ_d σₙd A) := by
  intro A
  constructor
  · -- 1.
    exact Blindparatopism.main_imp σ_d σₙd A
  · -- 2.
    rintro HA
    have HA' := Blindparatopism.main_imp σ_d.symm (λ x => (σₙd (σ_d x)).symm) (Blindparatopism σ_d σₙd A) HA ; clear HA
    have : Blindparatopism σ_d.symm (λ x => (σₙd (σ_d x)).symm) (Blindparatopism σ_d σₙd A) = A := by
      unfold Blindparatopism
      ext f
      rw [Set.mem_setOf_eq]
      constructor
      · -- 1.
        rintro ⟨a, ⟨ f, hf, rfl ⟩, rfl⟩
        simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        exact hf
      · -- 2.
        rintro hf
        use λ x => (σₙd (σ_d x)) (f (σ_d x))
        constructor
        · exact ⟨ f, hf, rfl ⟩
        · simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      done
    rw [← this]
    exact HA'
    done

-- Define Paratopism class
class Paratopism (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (σ_d : Fin d ≃ Fin d)
  (σₙd : Fin d → Fin n ≃ Fin n)
  (para : toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, {b : Fin d → Fin n | ∃ a ∈ A.set, b = (λ x => (σₙd (σ_d x)) ((a (σ_d x))))}, 
      Blindparatopism.main_imp σ_d σₙd A.set A.prop ⟩)
  (inv_para : toEquiv.invFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, Blindparatopism σ_d.symm (fun x => (σₙd (σ_d x)).symm) A.set, 
      Blindparatopism.main_imp σ_d.symm (λ x => (σₙd (σ_d x)).symm) A.set A.prop ⟩)

----------------------------------------------------------------------------------------------

instance { n d : Nat} : Group (Isotopism n d) where
  one := ⟨ Equiv.refl (LatinHypercube n d), λ x => Equiv.refl (Fin n), by simp; rfl, by simp; rfl ⟩
  mul := λ A B : Isotopism n d => ⟨ Equiv.trans A.toEquiv B.toEquiv, λ x => Equiv.trans (A.σₙd x) (B.σₙd x), 
    by ext A1; simp; , ?_ ⟩
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

