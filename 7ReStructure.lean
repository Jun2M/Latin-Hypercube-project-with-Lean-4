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

def LatinHyperplane {n d : Nat} (Hd : d > 2) (A : LatinHypercube n d) (f : Fin d → Fin n) (x : Fin d) : 
LatinHypercube n (d-1) := 
  ⟨ ⟨ A.H0.1, Nat.lt_sub_of_add_lt Hd ⟩,
    { a : Fin (d-1) → Fin n // ∃ a' : Fin d → Fin n, a' ∈ A.set ∧ ∀ y : Fin (d-1), a y = a' (Fin.succ_above x y) },
    by
      intro a
      simp only [LatinHypercube.set, is_LatinHypercube, LatinHypercube.prop, LatinHypercube.H0, 
        gt_iff_lt, ne_eq, dite_eq_ite]
      intro f x
      specialize a (λ y => f (Fin.succ_above x y)) (Fin.succ_above x x)
      rcases a with ⟨ a', ha'1, ha'2 ⟩
      use a'
      constructor
      · -- 1.
        refine ⟨ ha'1.1, ?_ ⟩ ; clear ha'2
        intro y
        rw [Fin.succ_above_ne]
        done
      · -- 2.
        intro a'' ha''
        suffices h : a'' = a' by rw [h]
        apply ha'2 _ ⟨ ha''.1, ?_ ⟩ ; clear ha'2 a' ha'' A
        intro y
        rw [Fin.succ_above_ne]
        done
      done
  ⟩
  

-- Define Isotopism class
def BlindIsotopism {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = (λ x => σₙd x (a x))}

lemma BlindIsotopism.main_imp {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (BlindIsotopism σₙd A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1 <;> simp only [H0, if_true, if_false] ; clear H0
  · -- 1.
    rintro HA f x
    specialize HA (λ x => (σₙd x).symm (f x)) x
    rcases HA with ⟨a', ha'1, ha'2⟩
    use λ x => σₙd x (a' x)
    constructor <;> simp only [BlindIsotopism, and_imp]
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

theorem BlindIsotopism.main {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (BlindIsotopism σₙd A) := by
  refine ⟨ BlindIsotopism.main_imp σₙd A, ?_ ⟩
  rintro HA
  have HA' := BlindIsotopism.main_imp (λ x => (σₙd x).symm) (BlindIsotopism σₙd A) HA ; clear HA
  suffices H : BlindIsotopism (fun x => (σₙd x).symm) (BlindIsotopism σₙd A) = A by rw [← H] ; exact HA'
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

lemma BlindIsotopism.closed_under_comp {n d : Nat} (σₙd1 σₙd2 : Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n) ) :
  BlindIsotopism σₙd1 (BlindIsotopism σₙd2 A) = BlindIsotopism (λ x => Equiv.trans (σₙd2 x) (σₙd1 x)) A := by
  unfold BlindIsotopism Equiv.trans
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

lemma BlindIsotopism.closed_under_inv {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (BlindIsotopism σₙd) (BlindIsotopism (λ x => (σₙd x).symm)) := by
  unfold BlindIsotopism Equiv.symm Function.RightInverse Function.LeftInverse
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

lemma BlindIsotopism.closed_under_inv1 {n d : Nat} (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (BlindIsotopism σₙd) (BlindIsotopism (λ x => (σₙd x).symm)) := by
  unfold BlindIsotopism Function.LeftInverse
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
    ⟨ A.H0, BlindIsotopism σₙd A.set, BlindIsotopism.main_imp σₙd A.set A.prop ⟩)

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
  ⟨ Equiv.refl (LatinHypercube n d), by use λ _ => Equiv.refl (Fin n); unfold BlindIsotopism; simp; rfl ⟩

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
      rw [BlindIsotopism.closed_under_comp σₙd2 σₙd1 A.set]
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
    nth_rw 1 [← BlindIsotopism.closed_under_inv1 σₙd A.set]
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

def BlindConjugation {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := {b : Fin d → Fin n | ∃ a ∈ A, b = a ∘ σ_d}

lemma BlindConjugation.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  ∀ A : Set (Fin d → Fin n), is_LatinHypercube A → is_LatinHypercube (BlindConjugation σ_d A) := by
  intro A
  unfold is_LatinHypercube
  simp only [gt_iff_lt, ne_eq, dite_eq_ite]

  by_cases H0 : n > 0 ∧ d > 1 <;> simp only [H0, if_true, if_false] ; clear H0
  intro HA f x 
  specialize HA (λ x => f (σ_d.symm x)) (σ_d x)
  rcases HA with ⟨a', ha'1, ha'2⟩
  use λ x => a' (σ_d x)
  simp only [and_imp, BlindConjugation]
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

theorem BlindConjugation.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (BlindConjugation σ_d A) := by
  refine ⟨ BlindConjugation.main_imp σ_d A, ?_ ⟩
  rintro HA
  have HA' := BlindConjugation.main_imp σ_d.symm (BlindConjugation σ_d A) HA ; clear HA
  suffices H : BlindConjugation σ_d.symm (BlindConjugation σ_d A) = A by rw [← H]; exact HA'
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

lemma BlindConjugation.closed_under_comp {n d : Nat} (σ_d1 σ_d2 : Fin d ≃ Fin d) (A : Set (Fin d → Fin n) ) :
  BlindConjugation σ_d1 (BlindConjugation σ_d2 A) = BlindConjugation (Equiv.trans σ_d1 σ_d2) A := by
  unfold BlindConjugation Equiv.trans
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
  
lemma BlindConjugation.closed_under_inv {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.RightInverse (@BlindConjugation n _ σ_d) (@BlindConjugation n _ σ_d.symm) := by
  unfold BlindConjugation Function.RightInverse Function.LeftInverse
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


lemma BlindConjugation.closed_under_inv1 {n d : Nat} (σ_d : Fin d ≃ Fin d) :
  Function.LeftInverse (@BlindConjugation n _ σ_d) (@BlindConjugation n _ σ_d.symm) := by
  unfold BlindConjugation Function.LeftInverse
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
    ⟨ A.H0, BlindConjugation σ_d A.set, BlindConjugation.main_imp σ_d A.set A.prop ⟩)

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

theorem Conjugation.ext_iff {n d : Nat} (T1 T2 : Conjugation n d) :
  T1 = T2 ↔ T1.toFun = T2.toFun :=  ⟨ λ h => h ▸ rfl, Conjugation.ext T1 T2 ⟩

def Conjugation.id {n d : Nat} : Conjugation n d :=
  ⟨ Equiv.refl (LatinHypercube n d), by use Equiv.refl (Fin d); unfold BlindConjugation; simp; rfl ⟩

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
      exact BlindConjugation.closed_under_comp σ_d2 σ_d1 A.set
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
    nth_rw 1 [← BlindConjugation.closed_under_inv1 σ_d A.set]
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

def BlindParatopism {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
    (A : Set (Fin d → Fin n)) : 
  Set (Fin d → Fin n) := BlindConjugation σ_d (BlindIsotopism σₙd A)

lemma BlindParatopism.main_imp {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
(A : Set (Fin d → Fin n)) :
  is_LatinHypercube A → is_LatinHypercube (BlindParatopism σ_d σₙd A) := by
  intro HA
  apply BlindConjugation.main_imp σ_d (BlindIsotopism σₙd A)
  exact BlindIsotopism.main_imp σₙd A HA

theorem BlindParatopism.main {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) 
(A : Set (Fin d → Fin n)) :
  is_LatinHypercube A ↔ is_LatinHypercube (BlindParatopism σ_d σₙd A) := by
  rw [BlindIsotopism.main σₙd, BlindConjugation.main σ_d (BlindIsotopism σₙd A)]
  rfl
  done

lemma BlindParatopism.closed_under_comp {n d : Nat} (σ_d1 σ_d2 : Fin d ≃ Fin d) (σₙd1 σₙd2 : 
  Fin d → Fin n ≃ Fin n) (A : Set (Fin d → Fin n) ) :
  BlindParatopism σ_d1 σₙd1 (BlindParatopism σ_d2 σₙd2 A) = 
  BlindParatopism (Equiv.trans σ_d1 σ_d2) (λ x => Equiv.trans (σₙd2 x) (σₙd1 (σ_d2.symm x))) A := by
  unfold BlindParatopism BlindConjugation BlindIsotopism
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

lemma BlindParatopism.closed_under_inv {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.RightInverse (BlindParatopism σ_d σₙd) (BlindParatopism σ_d.symm (λ x => (σₙd (σ_d x)).symm)) := by
  unfold BlindParatopism BlindConjugation BlindIsotopism Function.RightInverse Function.LeftInverse
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

lemma BlindParatopism.closed_under_inv1 {n d : Nat} (σ_d : Fin d ≃ Fin d) (σₙd : Fin d → Fin n ≃ Fin n) :
  Function.LeftInverse (BlindParatopism σ_d σₙd) (BlindParatopism σ_d.symm (λ x => (σₙd (σ_d x)).symm)) := by
  unfold BlindParatopism BlindConjugation BlindIsotopism Function.LeftInverse
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
  ⟨ A.H0, BlindParatopism σ_d σₙd A.set, BlindParatopism.main_imp σ_d σₙd A.set A.prop ⟩)

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

theorem Paratopism.ext_iff {n d : Nat} (T1 T2 : Paratopism n d) :
  T1 = T2 ↔ T1.toFun = T2.toFun :=  ⟨ λ h => h ▸ rfl, Paratopism.ext T1 T2 ⟩

def Paratopism.id {n d : Nat} : Paratopism n d :=
  ⟨ Equiv.refl (LatinHypercube n d), by 
    use Equiv.refl (Fin d)
    use fun _ => Equiv.refl (Fin n)
    unfold BlindParatopism BlindConjugation BlindIsotopism
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
      rw [BlindParatopism.closed_under_comp σ_d2 σ_d1 σₙd2 σₙd1 A.set]
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
    nth_rw 1 [← BlindParatopism.closed_under_inv1 σ_d σₙd A.set]
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

-- Quotienting by the equivalence Relation

def Isotopism.Relation {n d : Nat} : LatinHypercube n d → LatinHypercube n d → Prop := 
  λ A B => ∃ T : Isotopism n d, T.toFun A = B

lemma Isotopism.Relation.refl {n d : Nat} : Reflexive (@Isotopism.Relation n d) := 
  fun _ => ⟨ Isotopism.id, rfl ⟩

lemma Isotopism.Relation.symm {n d : Nat} : Symmetric (@Isotopism.Relation n d) := by
  rintro A B ⟨T, rfl⟩
  use T⁻¹
  have := mul_inv_self T
  rw [Isotopism.ext_iff, Function.funext_iff] at this
  exact this A
  done

lemma Isotopism.Relation.trans {n d : Nat} : Transitive (@Isotopism.Relation n d) := by
  rintro A B C ⟨T1, rfl⟩ ⟨T2, rfl⟩
  use Isotopism.comp T1 T2
  unfold Equiv.toFun toEquiv Isotopism.comp Equiv.trans Function.comp
  simp only [Equiv.toFun_as_coe]
  rfl
  done

def Isotopism.Relation.setoid {n d : Nat} : Setoid (LatinHypercube n d) :=
⟨ 
  Isotopism.Relation, 
  ⟨ Isotopism.Relation.refl, @Isotopism.Relation.symm n d, @Isotopism.Relation.trans n d ⟩
⟩

def Isotopism.Class (n d : Nat) := 
  Quotient (Isotopism.Relation.setoid : Setoid (LatinHypercube n d))

------------------------------------------------------------------------

def Conjugation.Relation {n d : Nat} : LatinHypercube n d → LatinHypercube n d → Prop := 
  λ A B => ∃ T : Conjugation n d, T.toFun A = B

lemma Conjugation.Relation.refl {n d : Nat} : Reflexive (@Conjugation.Relation n d) :=
  fun _ => ⟨ Conjugation.id, rfl ⟩

lemma Conjugation.Relation.symm {n d : Nat} : Symmetric (@Conjugation.Relation n d) := by
  rintro A B ⟨T, rfl⟩
  use T⁻¹
  have := mul_inv_self T
  rw [Conjugation.ext_iff, Function.funext_iff] at this
  exact this A
  done

lemma Conjugation.Relation.trans {n d : Nat} : Transitive (@Conjugation.Relation n d) := by
  rintro A B C ⟨T1, rfl⟩ ⟨T2, rfl⟩
  use Conjugation.comp T1 T2
  unfold Equiv.toFun toEquiv Conjugation.comp Equiv.trans Function.comp
  simp only [Equiv.toFun_as_coe]
  rfl
  done

def Conjugation.Relation.setoid {n d : Nat} : Setoid (LatinHypercube n d) :=
⟨ 
  Conjugation.Relation,
  ⟨ Conjugation.Relation.refl, @Conjugation.Relation.symm n d, @Conjugation.Relation.trans n d ⟩
⟩

def Conjugation.class (n d : Nat) := 
  Quotient (Conjugation.Relation.setoid : Setoid (LatinHypercube n d))

------------------------------------------------------------------------

def Paratopism.Relation {n d : Nat} : LatinHypercube n d → LatinHypercube n d → Prop := 
  λ A B => ∃ T : Paratopism n d, T.toFun A = B
  
lemma Paratopism.Relation.refl {n d : Nat} : Reflexive (@Paratopism.Relation n d) := 
  fun _ => ⟨ Paratopism.id, rfl ⟩

lemma Paratopism.Relation.symm {n d : Nat} : Symmetric (@Paratopism.Relation n d) := by
  rintro A B ⟨T, rfl⟩
  use T⁻¹
  have := mul_inv_self T
  rw [Paratopism.ext_iff, Function.funext_iff] at this
  exact this A
  done

lemma Paratopism.Relation.trans {n d : Nat} : Transitive (@Paratopism.Relation n d) := by
  rintro A B C ⟨T1, rfl⟩ ⟨T2, rfl⟩
  use Paratopism.comp T1 T2
  unfold Equiv.toFun toEquiv Paratopism.comp Equiv.trans Function.comp
  simp only [Equiv.toFun_as_coe]
  rfl
  done

def Paratopism.Relation.setoid {n d : Nat} : Setoid (LatinHypercube n d) :=
⟨ 
  Paratopism.Relation,
  ⟨ Paratopism.Relation.refl, @Paratopism.Relation.symm n d, @Paratopism.Relation.trans n d ⟩
⟩

def Paratopism.class (n d : Nat) := 
  Quotient (Paratopism.Relation.setoid : Setoid (LatinHypercube n d))

------------------------------------------------------------------------

/-
"The stabilisers of a latin hypercube L under isotopism, Paratopism and isomorphism
are known respectively as the autotopism group, autoParatopism group and automorphism
group of L. We use respectively Is(L), Par(L) and Aut(L) to denote these groups. For
example, Aut(L) = {σ ∈ ∆d+1n | Lσ = L}."
-/

def Isotopism.Stabiliser {n d : Nat} (A : LatinHypercube n d) : Set (Isotopism n d) :=
  { T : Isotopism n d | T.toFun A = A }

def Conjugation.Stabiliser {n d : Nat} (A : LatinHypercube n d) : Set (Conjugation n d) :=
  { T : Conjugation n d | T.toFun A = A }

def Paratopism.Stabiliser {n d : Nat} (A : LatinHypercube n d) : Set (Paratopism n d) :=
  { T : Paratopism n d | T.toFun A = A }

------------------------------------------------------------------------

