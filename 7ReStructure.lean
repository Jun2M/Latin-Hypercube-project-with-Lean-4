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
    exact ⟨ λ x => (σₙd x) (f x), ⟨ f, ha, rfl ⟩, by simp only [Equiv.symm_apply_apply] ⟩
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

theorem Isotopism.ext_iff {n d : Nat} (T1 T2 : Isotopism n d) : 
  T1 = T2 ↔ T1.toFun = T2.toFun :=  ⟨ λ h => h ▸ rfl, Isotopism.ext T1 T2 ⟩

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
      rw [iso1, iso2, LatinHypercube.mk.injEq, Function.comp_apply] ; clear iso1 iso2
      simp only
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

theorem Isotopism.LeftInverse { n d : Nat} (T : Isotopism n d) : 
Isotopism.comp (Isotopism.inverse_map T) T  = Isotopism.id := by
  unfold Isotopism.comp Isotopism.inverse_map Isotopism.id Equiv.trans Function.comp
  congr <;>
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply] <;>
  rfl

instance Isotopism.Group {n d : Nat} : Group (Isotopism n d) := by
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


lemma Blindconjugate.closed_under_inv1 {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.LeftInverse (@Blindconjugate n _ σ_d) (@Blindconjugate n _ σ_d.symm) := by
  unfold Blindconjugate Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk, Function.comp]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ a, ha, rfl ⟩, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact ha
  · -- 2.
    rintro ha
    exact ⟨ λ x => f (σ_d.symm x), ⟨ f, ha, rfl ⟩, by simp only [Equiv.symm_apply_apply] ⟩
  done

class Conjugation (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (conj : ∃ σ_d : Fin d ≃ Fin d, toEquiv.toFun = λ A : (LatinHypercube n d) => 
    ⟨ A.H0, Blindconjugate σ_d A.set, Blindconjugate.main_imp σ_d A.set A.prop ⟩)

@[ext]
theorem Conjugation.ext {n d : Nat} (T1 T2 : Conjugation n d) : 
  T1.toFun = T2.toFun → T1 = T2 := by
  intro h
  have Conjugation.ext_equiv : T1.toEquiv = T2.toEquiv → T1 = T2 := by
    rcases T1 with ⟨ ⟨ f, f1, tofunf, invfunf ⟩, conj1 ⟩
    rcases T2 with ⟨ ⟨ g, g1, tofung, invfung ⟩, conj2 ⟩ 
    simp only [Equiv.mk.injEq, and_imp]
    rintro h1 h2
    congr
    done
  apply Conjugation.ext_equiv
  ext A
  rw [← Equiv.toFun_as_coe, ← Equiv.toFun_as_coe, h]

def Conjugation.id {n d : Nat} : Conjugation n d :=
  ⟨ Equiv.refl (LatinHypercube n d), by use Equiv.refl (Fin d); unfold Blindconjugate; simp; rfl ⟩

def Conjugation.comp {n d : Nat} (T1 T2 : Conjugation n d) : Conjugation n d :=
  ⟨ Equiv.trans T1.toEquiv T2.toEquiv,
    by
      rcases T1 with ⟨ _, ⟨ σ_d1, conj1 ⟩ ⟩
      rcases T2 with ⟨ _, ⟨ σ_d2, conj2 ⟩ ⟩
      simp only [Equiv.trans]
      use Equiv.trans σ_d2 σ_d1
      ext A
      rw [Equiv.toFun_as_coe] at conj1 conj2
      rw [conj1, conj2, LatinHypercube.mk.injEq, Function.comp_apply] ; clear conj1 conj2
      exact Blindconjugate.closed_under_comp σ_d2 σ_d1 A.set
      done
  ⟩

def Conjugation.inverse_map {n d : Nat} (T : Conjugation n d) : Conjugation n d :=
  ⟨ T.toEquiv.symm, by
    rcases T with ⟨ equiv, ⟨ σ_d, conj ⟩ ⟩
    use σ_d.symm
    ext A
    apply Equiv.injective equiv
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe_apply, Equiv.apply_symm_apply]
    rw [Equiv.toFun_as_coe] at conj
    rw [conj, LatinHypercube.mk.injEq]
    nth_rw 1 [← Blindconjugate.closed_under_inv1 σ_d A.set]
    done
  ⟩

theorem Conjugation.LeftInverse {n d : Nat} (T : Conjugation n d) : 
Conjugation.comp (Conjugation.inverse_map T) T = Conjugation.id := by
  unfold Conjugation.comp Conjugation.inverse_map Conjugation.id Equiv.trans Function.comp
  congr <;>
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply] <;>
  rfl

instance Conjugation.Group {n d : Nat} : Group (Conjugation n d) := by
  refine'
  {
    mul := λ T1 T2 : Conjugation n d => Conjugation.comp T1 T2
    one := Conjugation.id
    inv := λ T : Conjugation n d => Conjugation.inverse_map T
    div := λ T1 T2 : Conjugation n d => Conjugation.comp T1 (Conjugation.inverse_map T2)
    npow := @npowRec _ ⟨Conjugation.id⟩ ⟨λ T1 T2 => Conjugation.comp T1 T2⟩
    zpow := @zpowRec _ ⟨Conjugation.id⟩ ⟨λ T1 T2 => Conjugation.comp T1 T2⟩ ⟨Conjugation.inverse_map⟩
    mul_left_inv := fun T => Conjugation.LeftInverse T
    .. } <;>
  intros <;>
  ext <;>
  rfl
  done

--------------------------------------------------------------------------

def Blindparatopism {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := Blindconjugate σ_d (Blindisotopism σₙd A)

lemma Blindparatopism.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
(A : Set (Fin d → Fin n)) :
  is_LatinHypercube A → is_LatinHypercube (Blindparatopism σ_d σₙd A) := by
  intro HA
  apply Blindconjugate.main_imp σ_d (Blindisotopism σₙd A)
  exact Blindisotopism.main_imp σₙd A HA

theorem Blindparatopism.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
(A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (Blindparatopism σ_d σₙd A) := by
  rw [Blindisotopism.main σₙd, Blindconjugate.main σ_d (Blindisotopism σₙd A)]
  rfl
  done

lemma Blindparatopism.closed_under_comp {n d : Nat} (σ_d1 σ_d2 : Fin d ≃ Fin d) (σₙd1 σₙd2 : 
  Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n) ) :
  Blindparatopism σ_d1 σₙd1 (Blindparatopism σ_d2 σₙd2 A) = 
  Blindparatopism (Equiv.trans σ_d1 σ_d2) (λ x => Equiv.trans (σₙd2 x) (σₙd1 (σ_d2.symm x))) A := by
  unfold Blindparatopism Blindconjugate Blindisotopism
  simp only [Set.mem_setOf_eq, Equiv.trans_apply, Equiv.coe_trans]
  ext a
  constructor
  · -- 1.
    rintro ⟨_, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, rfl⟩
    simp [Function.comp]
    refine ⟨ fun x => (σₙd1 (σ_d2.symm x)) ((σₙd2 x) (a x)), ?_, by simp only [Equiv.symm_apply_apply] ⟩
    exact ⟨ a, ha, rfl ⟩
  · -- 2.
    rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨ _, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, ?_ ⟩
    ext x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  done

lemma Blindparatopism.closed_under_inv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (Blindparatopism σ_d σₙd) (Blindparatopism σ_d.symm (λ x => (σₙd (σ_d x)).symm)) := by
  unfold Blindparatopism Blindconjugate Blindisotopism Function.RightInverse Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk, Function.comp]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, rfl⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact ha
  · -- 2.
    rintro ha
    refine ⟨ _, ⟨ _, ⟨ _, ⟨ _, ha, rfl ⟩, rfl ⟩, rfl ⟩, 
      by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] ⟩
  done

lemma Blindparatopism.closed_under_inv1 {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (Blindparatopism σ_d σₙd) (Blindparatopism σ_d.symm (λ x => (σₙd (σ_d x)).symm)) := by
  unfold Blindparatopism Blindconjugate Blindisotopism Function.LeftInverse
  simp only [Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.coe_fn_mk, Function.comp]
  rintro A
  ext f
  constructor
  · -- 1.
    rintro ⟨_, ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩, rfl⟩
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact ha
  · -- 2.
    rintro ha
    refine ⟨ _, ⟨ _, ⟨ _, ⟨ _, ha, rfl ⟩, rfl ⟩, rfl ⟩, 
      by simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] ⟩
  done

class Paratopism (n d : Nat) extends Equiv (LatinHypercube n d) (LatinHypercube n d) where
  (para : ∃ σ_d : Fin d ≃ Fin d, ∃ σₙd : Fin d → Fin n ≃ Fin n, toEquiv.toFun = λ A => 
  ⟨ A.H0, Blindparatopism σ_d σₙd A.set, Blindparatopism.main_imp σ_d σₙd A.set A.prop ⟩)

@[ext]
theorem Paratopism.ext {n d : Nat} (T1 T2 : Paratopism n d) : 
  T1.toFun = T2.toFun → T1 = T2 := by
  intro h
  have Paratopism.ext_equiv : T1.toEquiv = T2.toEquiv → T1 = T2 := by
    rcases T1 with ⟨ ⟨ f, f1, tofunf, invfunf ⟩, para1 ⟩
    rcases T2 with ⟨ ⟨ g, g1, tofung, invfung ⟩, para2 ⟩ 
    simp only [Equiv.mk.injEq, and_imp]
    rintro h1 h2
    congr
    done
  apply Paratopism.ext_equiv
  ext A
  rw [← Equiv.toFun_as_coe, ← Equiv.toFun_as_coe, h]

def Paratopism.id {n d : Nat} : Paratopism n d :=
  ⟨ Equiv.refl (LatinHypercube n d), by 
    use Equiv.refl (Fin d)
    use fun _ => Equiv.refl (Fin n)
    unfold Blindparatopism Blindconjugate Blindisotopism
    simp only [Equiv.toFun_as_coe, Equiv.coe_refl, Equiv.refl_apply, exists_eq_right', Set.setOf_mem_eq,
      Function.comp.right_id]
    rfl 
  ⟩

def Paratopism.comp {n d : Nat} (T1 T2 : Paratopism n d) : Paratopism n d :=
  ⟨ Equiv.trans T1.toEquiv T2.toEquiv,
    by 
      rcases T1 with ⟨ equiv1, ⟨ σ_d1, σₙd1, iso1 ⟩ ⟩
      rcases T2 with ⟨ equiv2, ⟨ σ_d2, σₙd2, iso2 ⟩ ⟩
      simp only [Equiv.trans]
      use (Equiv.trans σ_d2 σ_d1) 
      use λ x => Equiv.trans (σₙd1 x) (σₙd2 (σ_d1.symm x))
      ext A
      rw [Equiv.toFun_as_coe] at iso1 iso2
      rw [iso1, iso2, LatinHypercube.mk.injEq, Function.comp_apply] ; clear iso1 iso2
      simp only
      rw [Blindparatopism.closed_under_comp σ_d2 σ_d1 σₙd2 σₙd1 A.set]
      done
  ⟩

def Paratopism.inverse_map {n d : Nat} (T : Paratopism n d) : Paratopism n d :=
  ⟨ T.toEquiv.symm, by
    rcases T with ⟨ equiv, ⟨ σ_d, σₙd, para ⟩ ⟩
    use σ_d.symm
    use λ x => (σₙd (σ_d x)).symm
    ext A
    apply Equiv.injective equiv
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe_apply, Equiv.apply_symm_apply]
    rw [Equiv.toFun_as_coe] at para
    rw [para, LatinHypercube.mk.injEq]
    nth_rw 1 [← Blindparatopism.closed_under_inv1 σ_d σₙd A.set]
    done
  ⟩

theorem Paratopism.LeftInverse {n d : Nat} (T : Paratopism n d) :
Paratopism.comp (Paratopism.inverse_map T) T = Paratopism.id := by
  unfold Paratopism.comp Paratopism.inverse_map Paratopism.id Equiv.trans Function.comp
  congr <;>
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply] <;>
  rfl

instance Paratopism.Group {n d : Nat} : Group (Paratopism n d) := by
  refine'
  {
    mul := λ T1 T2 : Paratopism n d => Paratopism.comp T1 T2
    one := Paratopism.id
    inv := λ T : Paratopism n d => Paratopism.inverse_map T
    div := λ T1 T2 : Paratopism n d => Paratopism.comp T1 (Paratopism.inverse_map T2)
    npow := @npowRec _ ⟨Paratopism.id⟩ ⟨λ T1 T2 => Paratopism.comp T1 T2⟩
    zpow := @zpowRec _ ⟨Paratopism.id⟩ ⟨λ T1 T2 => Paratopism.comp T1 T2⟩ ⟨Paratopism.inverse_map⟩
    mul_left_inv := fun T => Paratopism.LeftInverse T
    .. } <;>
  intros <;>
  ext <;>
  rfl
  done

--------------------------------------------------------------------------

/-
"The stabilisers of a latin hypercube L under isotopism, paratopism and isomorphism
are known respectively as the autotopism group, autoparatopism group and automorphism
group of L. We use respectively Is(L), Par(L) and Aut(L) to denote these groups. For
example, Aut(L) = {σ ∈ ∆d+1n | Lσ = L}."
-/

-- Quotienting by the equivalence relation

def Isotopism.Relation {n d : Nat} : LatinHypercube n d → LatinHypercube n d → Prop := 
  λ A B => ∃ T : Isotopism n d, T.toFun A = B

lemma Isotopism.Relation.refl {n d : Nat} : Reflexive (@Isotopism.Relation n d) := 
  fun _ => ⟨ Isotopism.id, rfl ⟩

lemma Isotopism.Relation.symm {n d : Nat} : ∀ {x y : LatinHypercube n d}, 
  Isotopism.Relation x y → Isotopism.Relation y x  := by
  rintro A B ⟨T, rfl⟩
  use T⁻¹
  have := Isotopism.LeftInverse T
  rw [Isotopism.ext_iff] at this
  rw [← this]
  rw [Isotopism.LeftInverse T]
  done

lemma Isotopism.Relation.trans {n d : Nat} : ∀ {x y z : Set (Fin d → Fin n)}, 
  Isotopism.Relation x y → Isotopism.Relation y z → Isotopism.Relation x z := by
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

def Isotopism.Relation.setoid {n d : Nat} : Setoid (Set (Fin d → Fin n)) :=
⟨ 
  Isotopism.Relation, 
  ⟨ Isotopism.Relation.refl, Isotopism.Relation.symm, Isotopism.Relation.trans ⟩
⟩

def isotopism.class (n d : Nat) := 
  Quotient (Isotopism.Relation.setoid : Setoid (Set (Fin d → Fin n)))


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

