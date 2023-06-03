import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card

open Function
open Set

universe u

-- Some Function results that are useful

theorem ssub_by_non_mem {α : Type} {A B : Finset α} {a : α}
: A ⊆ B → a ∉ A → a ∈ B → A ⊂ B := by
  intros A_sub_B ainA not_ainB
  rw [ssubset_iff_subset_ne]
  refine ⟨ A_sub_B, ?_ ⟩ ; clear A_sub_B
  intro A_eq_B
  rw [A_eq_B] at ainA ; clear A_eq_B
  contradiction
  done

lemma SurjOn_of_image_B {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: Set.MapsTo f A B → Set.SurjOn f A B → (Finset.image f A) = B := by
  intro f_AtoB f_surj
  rw [Finset.ext_iff]
  intro b
  apply Iff.intro
  {
    intro b_in_image ; clear f_surj
    rw [Finset.mem_image] at b_in_image
    rcases b_in_image with ⟨ a, ainA, H ⟩
    rw [← H]
    exact f_AtoB ainA
  }
  {
    intro binB ; clear f_AtoB
    rw [Finset.mem_image]
    exact f_surj binB
  }
  done


lemma image_B_of_SurjOn {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: (Finset.image f A) = B → Set.SurjOn f A B := by
  intros image_eq_B b binB
  rw [Finset.ext_iff] at image_eq_B
  rw [Finset.mem_coe] at binB
  exact Finset.mem_image.mp ((image_eq_B b).mpr binB)
  done


theorem SurjOn_iff_image_B {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: Set.MapsTo f A B → (Set.SurjOn f A B ↔ (Finset.image f A) = B) := by

  intros f_AtoB
  apply Iff.intro
  exact SurjOn_of_image_B f_AtoB
  exact image_B_of_SurjOn
  done


theorem InjOn_of_le_card {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: Set.MapsTo f A B → Set.InjOn f A → A.card ≤ B.card := by
  intros f_AtoB f_inj
  exact Finset.card_le_card_of_inj_on f f_AtoB f_inj
  done


theorem SurjOn_of_le_card {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β} 
: Set.MapsTo f A B → Set.SurjOn f A B → B.card ≤ A.card := by

  intros f_AtoB f_surj
  rw [← SurjOn_of_image_B f_AtoB f_surj]
  exact Finset.card_image_le
  done


theorem BijOn_of_eq_card {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: Set.BijOn f A B → A.card = B.card := by

  intros H
  rcases H with ⟨ f_AtoB, f_inj, f_surj ⟩
  exact antisymm (InjOn_of_le_card f_AtoB f_inj) (SurjOn_of_le_card f_AtoB f_surj)
  done


lemma same_card_to_inj_surj {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: A.card = B.card → Set.MapsTo f A B → Set.InjOn f A → Set.SurjOn f A B := by

  intros same_card f_AtoB f_inj b binB
  by_contra h
  have : Finset.image f A ⊂ B
  {
    apply ssub_by_non_mem (Finset.image_subset_iff.mpr f_AtoB) _ binB
    rw [Finset.mem_image]
    exact h
  } ; clear h f_AtoB binB
  have card_lt := Finset.card_lt_card this ; clear this
  rw [Finset.card_image_of_injOn f_inj, same_card] at card_lt
  exact lt_irrefl _ card_lt
  done


lemma same_card_to_surj_inj {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: A.card = B.card → Set.MapsTo f A B → Set.SurjOn f A B → Set.InjOn f A := by
  intros same_card f_AtoB f_surj
  rw [← SurjOn_of_image_B f_AtoB f_surj] at same_card
  exact Finset.injOn_of_card_image_eq same_card.symm
  done


theorem same_card_of_inj_iff_surj {α β : Type} [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}
: A.card = B.card → Set.MapsTo f A B → (Set.InjOn f A ↔ Set.SurjOn f A B) := by
  intros same_card f_AtoB
  apply Iff.intro
  exact same_card_to_inj_surj same_card f_AtoB
  exact same_card_to_surj_inj same_card f_AtoB
  done


-- theorem inj_MapsTo_self {len : ℕ} {f : (Fin len) → (Fin len)} (H : Injective f) :
--   (Finset.image f Finset.univ) = Finset.univ := by
--   have image_sub_domain : (Finset.image f Finset.univ) ⊆ Finset.univ := (Finset.image f Finset.univ).subset_univ
--   obtain image_eq_domain | image_ssub_domain := image_sub_domain.eq_or_ssubset ; clear image_sub_domain
--   exact image_eq_domain

--   exfalso
--   have MapsTo : Set.MapsTo f (coe Finset.univ) (coe (Finset.image f Finset.univ))
--   {
--     intros a ha
--     rw [Finset.mem_coe] at ha
--     rw [Finset.mem_coe]
--     rw [Finset.mem_image]
--     use a
--     exact ⟨ ha rfl ⟩
--   }

--   have card_image_ssub_domain := Finset.card_lt_card image_ssub_domain
--   have := Finset.exists_ne_map_eq_of_card_lt_of_MapsTo card_image_ssub_domain MapsTo
--   rcases this with ⟨ a, a_ext, b, b_ext, a_neq_b, H1 ⟩
--   exact a_neq_b (H H1)
--   done


lemma surj_of_inj {len : ℕ} {f : (Fin len) → (Fin len)} (H : Injective f) : Surjective f := by

  intros i
  have i_in_image : i ∈ Finset.univ := Finset.mem_univ i

  rw [← inj_MapsTo_self H] at i_in_image
  rw [Finset.mem_image] at i_in_image
  rcases i_in_image with ⟨ j, j_in_univ, j_MapsTo_i ⟩
  exact ⟨ j, j_MapsTo_i ⟩
  done


theorem bij_of_inj {len : ℕ} {f : (Fin len) → (Fin len)} (H : Injective f) : Bijective f :=
⟨ H, surj_of_inj H ⟩

theorem inv_fun_of_inj {len : ℕ} {f : (Fin len) → (Fin len)} (H : Injective f) :
 ∃ g : (Fin len) → (Fin len), RightInverse f g ∧ LeftInverse f g :=
  Function.bijective_iff_has_inverse.1 (bij_of_inj H)

theorem right_inv_ext {α β : Type} {f : α → β} {g : β → α} (H : RightInverse f g) (x : α) : g (f x) = x := H x
  -- what!!! that is so good


-- Now some results from Set theory

structure fSet' (α β : Type) :=
  (Set : Set (α × β))
  (is_fSet  : ∀ x : α, ∃! y : β, (x, y) ∈ Set)

structure bij_fSet' (α β : Type) extends fSet' α β :=
  (inv_fSet : ∀ y : β, ∃! x : α, (x, y) ∈ Set)


def is_αsurj  {α β : Type} (A : Set (α × β)) : Prop := ∀ x : α, ∃ y : β, (x, y) ∈ A
def is_αinj   {α β : Type} (A : Set (α × β)) : Prop := ∀ x : α, ∀ y1 y2 : β, (x, y1) ∈ A → (x, y2) ∈ A → y1 = y2
def is_βsurj {α β : Type} (A : Set (α × β)) : Prop := ∀ y : β, ∃ x : α, (x, y) ∈ A
def is_βinj  {α β : Type} (A : Set (α × β)) : Prop := ∀ y : β, ∀ x1 x2 : α, (x1, y) ∈ A → (x2, y) ∈ A → x1 = x2

def is_fun {α β : Type} (A : Set (α × β)) : Prop := is_αsurj A ∧ is_αinj A
def is_bij {α β : Type} (A : Set (α × β)) : Prop := is_fun A ∧ is_βsurj A ∧ is_βinj A


structure fSet (α β : Type) :=
  (Set : Set (α × β))
  (is_αsurj : ∀ x : α, ∃ y : β, (x, y) ∈ Set)
  (is_αinj  : ∀ x : α, ∀ y1 y2 : β (x, y1) ∈ Set → (x, y2) ∈ Set → y1 = y2)
  (is_fSet  : ∀ x : α, ∃! y : β (x, y) ∈ Set)

structure bij_fSet (α β : Type) extends fSet α β :=
  (is_βsurj : ∀ y : β, ∃ x : α, (x, y) ∈ Set)
  (is_βinj  : ∀ y : β, ∀ x1 x2 : α, (x1, y) ∈ Set → (x2, y) ∈ Set → x1 = x2)
  (inv_fSet : ∀ y : β, ∃! x : α, (x, y) ∈ Set)


@[ext]
lemma fSet_ext {α β : Type} {A B : fSet α β} (H : A.Set = B.Set) : A = B := by
  cases A
  cases B
  congr
  
  exact H
  done

-- theorem is_fSet_iff {α β : Type} {A : Set (α × β)} : is_fun A ↔ ∀ x : α ∃! y : β (x y) ∈ A := by
-- 
--   split
--   {
--     rintros ⟨ H1 H2 ⟩ x
--     use (H1 x).some
--     refine ⟨ (H1 x).some_spec _ ⟩

--       intros y H3
--       exact H2 x y (H1 x).some H3 (H1 x).some_spec
--   }
--   {
--     intro H
--     split;
--     intros x;
--     rcases H x with ⟨ y H1 H2 ⟩

--       exact ⟨ y H1 ⟩
    
--       intros y1 y2 H3 H4
--       rw H2 y1 H3
--       rw H2 y2 H4
    
--   }
--   done

def to_fSet {α β : Type} (A' : fSet' α β ) : fSet α β := by
  ⟨
    A'.Set
    λ x (A'.is_fSet x).exists
    λ x y1 y2 H1 H2 (A'.is_fSet x).unique H1 H2
    A'.is_fSet
  ⟩

def equiv_fun_fSet {α β : Type} (f : α → β) (A : fSet α β) : Prop := by 
  (∀ x : α ∀ y : β (x y) ∈ A.Set ↔ y = f x)


def fun_to_fSet {α β : Type} (f : α → β) : fSet α β := by 
  ⟨
    { p : α × β | p.2 = f p.1 }

    
      intros x
      use f x
      simp
      done
    
      simp only [Set.mem_Set_of_eq]
      intros x y1 y2 H1 H2
      rw H1
      rw H2
      done
    
      intros x
      use f x
      simp
      done
  ⟩
noncomputable def fSet_to_fun {α β : Type} (A : fSet α β) : α → β := by λ x (A.2 x).some


-- theorem fun_to_fSet_justification {α β : Type} (f : α → β) : is_fun (fun_to_fSet f) := by
-- 
--   unfold fun_to_fSet
--   rw is_fSet_iff
  
--   intros x
--   use f x
--   simp
--   done

theorem αsurj_of_fun_to_fSet {α β : Type} (f : α → β) : ∃ A : fSet α β equiv_fun_fSet f A := by

  use fun_to_fSet f
  unfold fun_to_fSet
  intros x y
  simp only [iff_self Set.mem_Set_of_eq]
  done

theorem αsurj_of_fSet_to_fun {α β : Type} (A : fSet α β) : ∃ f : α → β equiv_fun_fSet f A := by

  use fSet_to_fun A
  unfold fSet_to_fun
  intros x y
  simp only []
  have H1 := by (A.2 x).some_spec
  split;
  intro H2

    exact A.3 x y (A.2 x).some H2 H1

    rw H2
    exact H1
  done

theorem αinj_of_fSet_to_fun {α β : Type} (A : fSet α β) : ∀ f1 f2 : α → β equiv_fun_fSet f1 A → equiv_fun_fSet f2 A → f1 = f2 := by

  intros f1 f2 H1 H2
  ext x
  apply A.3 x (f1 x) (f2 x)
    rw H1 x (f1 x)
    rw H2 x (f2 x)
  done

theorem fun_fSet_RightInverse (α β : Type) : RightInverse (@fSet_to_fun α β) fun_to_fSet := by

  intro A
  ext p
  unfold fun_to_fSet fSet_to_fun
  rw Set.mem_Set_of_eq
  have H4 := by (A.2 p.1).some_spec

  split
    intro H1
    rw ← H1 at H4
    revert H4
    simp

    intro H3
    apply A.3 p.1 (p.2) ((A.2 p.1).some)
      revert H3
      simp

      exact H4
  done

theorem fun_fSet_LeftInverse (α β : Type) : LeftInverse (@fSet_to_fun α β) fun_to_fSet := by

  intro f
  ext x
  have := by ((fun_to_fSet f).2 x).some_spec
  revert this
  unfold fun_to_fSet fSet_to_fun
  simp
  done

theorem fun_to_fSet_bij (α β : Type) : bijective (@fun_to_fSet α β) := by

  split
    refine has_LeftInverse.Injective _
    unfold has_LeftInverse
    use fSet_to_fun
    exact fun_fSet_LeftInverse α β

    refine has_RightInverse.surjective _
    use fSet_to_fun
    exact fun_fSet_RightInverse α β
  done

-------------------------------------------------------------------------------------------------
-- Define latin square object
structure latin1 (len : ℕ):= by
  (nonempty : len > 0)
  (map : (Fin len) → (Fin len))
  (is_inj : Injective map)

-- nonempty from fin.pos


lemma latin1.ext {len : ℕ} (L1 L2 : latin1 len) : L1.map = L2.map → L1 = L2 := by

  intros H
  cases L1
  cases L2
  congr
  exact H
  done


lemma latin1.ext_iff {len : ℕ} (L1 L2 : latin1 len) : L1 = L2 ↔ L1.map = L2.map := by

  split
    intro H
    rw H
    apply latin1.ext
  done


theorem latin1_MapsTo_self {len : ℕ} (L : latin1 len) : (Finset.image L.map Finset.univ) = Finset.univ := by inj_MapsTo_self L.is_inj

lemma surj_of_latin1 {len : ℕ} (f : latin1 len) : surjective f.map := by surj_of_inj f.is_inj

theorem bij_of_latin1 {len : ℕ} (f : latin1 len) : bijective f.map := by bij_of_inj f.is_inj

-- theorem inv_of_latin1 {len : ℕ} (f : latin1 len) : ∃ g : latin1 len RightInverse f.map g.map ∧ LeftInverse f.map g.map := by
-- 
--   have fmap_bij := by bij_of_latin1 f
--   have : ∀ x : Fin len ∃ y : Fin len f.map y = x
--   {
--     intro x
--     have x_in_image : x ∈ Finset.univ := by Finset.mem_univ x
--     rw ← latin1_MapsTo_self f at x_in_image
--     rw Finset.mem_image at x_in_image
--     rcases x_in_image with ⟨ y y_in_univ y_MapsTo_x ⟩
--     exact ⟨ y y_MapsTo_x ⟩
--   }

--   have to_nat := by fin.fin_to_nat len

--   -- define inverse of fmap as a Function using nat.find
--   have exist_in_nat : ∀ x : Fin len ∃ y : ℕ f.map (@fin.of_nat' len (ne_zero.of_pos f.nonempty) y) = x
--   {
--     intro x
--     have := by this x
--     rcases this with ⟨ y y_MapsTo_x ⟩
--     use y.val
--     rw ← y_MapsTo_x
--     simp only [fin.coe_coe_eq_self fin.val_eq_coe eq_self_iff_true fin.of_nat'_eq_coe]
--   }

--   have fmap_inv : ∃ g : Fin len → Fin len ∀ x : Fin len f.map (g x) = x ∧ g (f.map x) = x
--   {
--     have g : Fin len → Fin len
--     {
--       intro x
--       cases exist_in_nat x
--       have := by nat.find (exist_in_nat x)
--       exact fin.of_nat' len (ne_zero.of_pos f.nonempty) this
--     }
--     have := by exist_in_nat x
--   }

--   -- use ⟨ f.nonempty fmap_inv _ ⟩

--   -- prove that fmap_inv is inverse of fmap
--   have fmap_inv_is_inv : RightInverse f.map fmap_inv ∧ LeftInverse f.map fmap_inv
--   {
--     split
--     {
--       intro x

--       rw ← (nat.find_spec (exist_in_nat x))
--       simp only [fin.of_nat'_eq_coe]
--       exact nat.find_min (exist_in_nat x) (nat.find_spec (exist_in_nat x))
--     }
--     {
--       intro x
--       have := by nat.find_spec (exist_in_nat x)
--       rw ← this
--       simp only [fin.of_nat'_eq_coe fin.coe_coe_eq_self fin.val_eq_coe eq_self_iff_true]
--       exact nat.find_min (exist_in_nat x) (nat.find_spec (exist_in_nat x))
--     }
--   }
  
--   done

-------------------------------------------------------------------------------------------------


-- structure latin1_hom (len : ℕ) : Type := by
--   (to_fun : latin1 len → latin1 len)


-- lemma latin1_hom.ext {len : ℕ} (f g : latin1_hom len) : f.to_fun = g.to_fun → f = g := by
-- 
--   intros H
--   cases f
--   cases g
--   congr
--   exact H
--   done


-- lemma latin1_hom.ext_iff {len : ℕ} (f g : latin1_hom len) : f = g ↔ f.to_fun = g.to_fun := by
-- 
--   split
--     intro H
--     rw H
--     apply latin1_hom.ext
--   done


theorem permi1 {len : ℕ} {g : (Fin len) → (Fin len)} (f : latin1 len) (g_inj : Injective g) : 
  ∃ fg : latin1 len fg.map = g ∘ f.map := by

  use { nonempty := by f.nonempty map := by g ∘ f.map is_inj := by (Injective.of_comp_iff g_inj f.map).mpr f.is_inj }
  done

theorem perme1 {len : ℕ} {g : (Fin len) → (Fin len)} (f : latin1 len) (g_inj : Injective g) : 
  ∃ gf : latin1 len gf.map = f.map ∘ g := by

  use { nonempty := by f.nonempty map := by f.map ∘ g is_inj := by (Injective.of_comp_iff f.is_inj g).mpr g_inj }
  done

theorem push1 {len : ℕ} (f : latin1 len) : ∃ f' : latin1 len LeftInverse f'.map f.map ∧ RightInverse f'.map f.map := by

  choose g hg using Function.bijective_iff_has_inverse.1 (bij_of_latin1 f)
  have g_inj : Injective g := by LeftInverse.Injective (Function.RightInverse.LeftInverse hg.2)
  use { nonempty := by f.nonempty map := by g is_inj := by g_inj }
  exact hg
  done

def is_normal1 {len : ℕ} (f : latin1 len) : Prop := by f.map = id



-- noncomputable def normalise_hom1 {len : ℕ} : latin1_hom len := by
-- 
--   refine ⟨ λ f _ ⟩
--   choose g hg using Function.bijective_iff_has_inverse.1 (bij_of_latin1 f)
--   have g_inj : Injective g := by LeftInverse.Injective (Function.RightInverse.LeftInverse hg.2)
--   exact (permi_hom1 g_inj).to_fun f
--   done


-- def latin1_hom_comp {len : ℕ} (f g : latin1_hom len) : latin1_hom len := by
-- 
--   refine ⟨ λ h _ ⟩
--   exact ((f.to_fun ∘ g.to_fun) h)
--   done


-- lemma id_hom1_id {len : ℕ} (f : latin1 len) : (id_hom1.to_fun f) = f := by
-- 
--   apply latin1.ext
--   unfold id_hom1
--   unfold permi_hom1
--   unfold latin1_hom.to_fun
--   unfold latin1.map
--   rw Function.comp.left_id
--   done


-- def latin1_equiv {len : ℕ} (f g : latin1 len) : Prop := by
--   ∃ hom : latin1_hom len hom.to_fun f = hom.to_fun g


-- lemma latin1_equiv_refl {len : ℕ} (f : latin1 len) : latin1_equiv f f := by
-- 
--   use id_hom1
--   done


-- lemma latin1_equiv_symm {len : ℕ} (f g : latin1 len) : latin1_equiv f g → latin1_equiv g f := by
-- 
--   intro H
--   rcases H with ⟨ hom H ⟩
--   use hom
--   exact H.symm
--   done


-- lemma normalise_hom1_returns_id {len : ℕ} (f : latin1 len) : (normalise_hom1.to_fun f).map = id := by
-- 
--   unfold normalise_hom1
--   unfold permi_hom1
--   apply Function.LeftInverse.id
--   exact (classical.some_spec (Function.bijective_iff_has_inverse.1 (bij_of_latin1 f))).1
--   done


-- theorem all_latin1_equiv {len : ℕ} (f g : latin1 len) : latin1_equiv f g := by
-- 
--   use normalise_hom1
--   rw latin1.ext_iff
--   rw normalise_hom1_returns_id
--   rw normalise_hom1_returns_id
--   done


-- structure latin1_isom (len : ℕ) : Type := by
--   (to_hom : latin1_hom len)
--   (inv : latin1_hom len)
--   (right_inv : to_hom.to_fun ∘ inv.to_fun = id )
--   (left_inv : inv.to_fun ∘ to_hom.to_fun = id )


-- lemma latin1_isom.ext {len : ℕ} (f g : latin1_isom len) : f.to_hom = g.to_hom → f = g := by
-- 
--   intros H
--   cases f
--   cases g
--   congr
--   exact H
--   sorry
--   done


-- lemma latin1_isom.ext_iff {len : ℕ} (f g : latin1_isom len) : f = g ↔ f.to_hom = g.to_hom := by
-- 
--   split
--     intro H
--     rw H
--     apply latin1_isom.ext
--   done


-- def perm_isom1 {len : ℕ} {g : (Fin len) → (Fin len)} (g_inj : Injective g) : latin1_isom len := by
-- {
--   to_hom := by permi_hom1 g_inj
--   inv := by 
--     {
--       to_fun := by 
--       
--         intro f
--         choose h hh using inv_fun_of_inj g_inj
--         refine ⟨ f.nonempty ( h ∘ f.map) _ ⟩
        
--         rw Injective.of_comp_iff
--         exact f.is_inj
--         exact LeftInverse.Injective (Function.RightInverse.LeftInverse hh.2)
--         done
--     }
--   right_inv := by
--   
--     simp
--     rw Function.comp.left_id
--     done
-- }