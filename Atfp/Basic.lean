import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Sum.Order
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Order.Category.CompleteLat
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Category.Semilat
import Mathlib.Order.FixedPoints

open CategoryTheory Limits MonoidalCategory

section Chapter1

end Chapter1

section Chapter2

section Section1

universe u

/-! Example 2.1.1 -/

variable {M : Type u} [inst : Monoid M]
#check Monoid
#check inst.one
#check inst.mul
#check inst.one_mul
#check inst.mul_one
#check inst.mul_assoc

/-! Example 2.1.2 -/

variable {X : Type u}

#check Nat.instAddMonoid

instance : Monoid (X → X) where
  one := @id X
  mul f g := f ∘ g
  one_mul := Function.id_comp
  mul_one := Function.comp_id
  mul_assoc := Function.comp_assoc

#check Matrix.semiring.toMonoidWithZero.toMonoid

#check FreeMonoid.instCancelMonoid.toMonoid

/-! Example 2.1.3 -/

variable [inst : Group X]
#check Group
#check inst.toMonoid
#check inv_mul_cancel
#check mul_inv_cancel

#check Int.instAddGroup

/-! Example 2.1.4 -/

-- For all x ∈ G, there exists a unique i such that x * i = i * x = e

/-! Example 2.1.5 -/

variable [inst : PartialOrder X]
#check PartialOrder
#check inst.le
#check inst.le_refl
#check inst.le_trans
#check inst.le_antisymm

/-! Example 2.1.6 -/

#check Nat.instPartialOrder

instance (priority := low) Nat.instPartialOrderDvd : PartialOrder ℕ where
  le a b := a ∣ b
  lt a b := a ∣ b ∧ ¬b ∣ a
  le_refl := Nat.dvd_refl
  le_trans _ _ _ := Nat.dvd_trans
  le_antisymm _ _ := Nat.dvd_antisymm

variable (α : Type u)
#synth PartialOrder (Set α)

instance {X : Type u} : PartialOrder (List X) where
  le w w' := ∃ w₀, w' = w ++ w₀
  le_refl w := ⟨[], List.append_nil w |>.symm⟩
  le_trans w w' w'' := by
    intro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    rw [h₂, h₁]
    exact ⟨w₁ ++ w₂, List.append_assoc w w₁ w₂⟩
  le_antisymm w w' := by
    intro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    simp_all

end Section1

section Section2

universe u

variable {M N : Type u} [Monoid M] [Monoid N] (f : MonoidHom M N)
#check MonoidHom
#check f.toFun
#check f.map_one
#check f.map_mul

variable (X Y : Pointed) (f : Pointed.Hom X Y)
#check Pointed
#check X.X
#check X.point
#check Pointed.Hom
#check f.toFun
#check f.map_point

variable {M' N' : Type u} [Group M'] [Group N'] (f : MonoidHom M' N')
#check f.toFun
#check f.map_one
#check f.map_mul
#check f.map_inv

section Section1

/-! Example 2.2.1 -/

variable [PartialOrder X] [PartialOrder Y] (f : OrderHom X Y)
#check OrderHom
#check f.toFun
#check f.monotone

end Section1

end Section2

section Section3

universe u

/-! Definition 2.3.1 -/

variable {𝓒 𝓓 : Type u} [inst : Category 𝓒] (X Y Z : 𝓒) (f : X ⟶ Y) (g : Y ⟶ Z)
#check Category
#check X ⟶ Y
#check 𝟙 X
#check f ≫ g
#check inst.id_comp
#check inst.comp_id
#check inst.assoc

section Section1

/-! Example 2.3.2 -/

#check types

/-! Example 2.3.3 -/

#check RelCat.instLargeCategory

/-! Example 2.3.4 -/

def Matrix.instCategory {S} [Semiring S] : Category ℕ where
  Hom m n := Matrix (Fin m) (Fin n) S
  id _ := 1
  comp f g := f * g
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc

/-! Example 2.3.5 -/

#check MonCat.instCategory

/-! Example 2.3.6 -/

#check GrpCat.instCategory

/-! Example 2.3.7 -/

#check PartOrd.instCategory

end Section1

section Section2

variable [inst : Category 𝓒] [inst' : Category 𝓓] (F : 𝓒 ⥤ 𝓓)
#check Functor
#check F.obj
#check F.map
#check F.map_id
#check F.map_comp

end Section2

section Section3

/-! Definition 2.3.8 -/

#check HasTerminal
#check hasTerminal_of_unique
#check terminal.from
#check terminal.hom_ext

/-! Definition 2.3.9 -/

#check HasInitial
#check hasInitial_of_unique
#check initial.to
#check initial.hom_ext

/-! Example 2.3.10 -/

#check Types.isTerminalPunit
#check Types.isInitialPunit

/-! Definition 2.3.11 -/
#check HasBinaryProducts
#check Limits.prod
#check prod.fst
#check prod.snd
#check prod.lift
#check prod.hom_ext
#check prod.map

/-! Example 2.3.12 -/

#check Types.binaryProductIso

/-! Example 2.3.13 -/

noncomputable def MonCat.prod (X Y : MonCat) : MonCat :=
  Limits.prod X Y

-- TODO: binary products in Mon

/-! Example 2.3.14 -/

instance [Category 𝓒] [Category 𝓓] : Category (𝓒 × 𝓓) := inferInstance

/-! Definition 2.3.15 -/

#check HasCoproducts
#check Limits.coprod
#check coprod.inl
#check coprod.inr
#check coprod.desc
#check coprod.hom_ext
#check coprod.map

/-! Example 2.3.16 -/

#check Types.coproductIso

/-! Example 2.3.17 -/

#check Monoid.Coprod

#check MonCat

/-! Definition 2.3.18 -/

#check ihom

-- TODO

end Section3

end Section3

end Chapter2

section Chapter3

universe u

section Section1

variable {α : Type u}

#check Nat
#check Nat.zero
#check Nat.succ
abbrev Nat.one := succ zero
abbrev Nat.two := succ one
abbrev Nat.three := succ two

def Nat.double : ℕ → ℕ
  | zero => zero
  | succ n => succ (succ (double n))

#check Nat.add
#check Nat.mul
#check Nat.repeat

def Nat.fold' (z : α) (s : α → α) : ℕ → α
  | zero => z
  | .succ n => s (fold' z s n)

def Nat.double' n := Nat.fold' zero (fun m => succ (succ m)) n
def Nat.add' m n := Nat.fold' (fun x => x) (fun r x => succ (r x)) m n
def Nat.mul' m n := Nat.fold' (fun _ => zero) (fun r x => Nat.add' (r x) x) m n

#eval Nat.add' 3 7
#eval Nat.mul' 3 7

def Nat.add'' m := Nat.fold' m succ
def Nat.mul'' m := Nat.fold' 0 (Nat.add m)

#eval Nat.add'' 3 7
#eval Nat.mul'' 3 7

end Section1

open Endofunctor

section Section2

namespace Section2

def N : Type u ⥤ Type u where
  obj X := PUnit ⊕ X
  map := Sum.map id
  map_id := by
    intro
    simp only [types, Sum.map_id_id]
    rfl
  map_comp := by
    intros
    ext
    simp [types_comp_apply, Sum.map_map]
    rfl

def D.Obj : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => N.obj (D.Obj n)

def D.step {n : ℕ} : D.Obj n → D.Obj (n + 1) := .inr

def D.mapLE {m : ℕ} : {n : ℕ} → m ≤ n → (D.Obj m → D.Obj n)
  | 0, h => Nat.le_zero.mp h ▸ id
  | n + 1, h =>
    if heq : m = n + 1 then
      heq ▸ id
    else
      D.step ∘ D.mapLE (by omega)

private theorem D.mapLE_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : D.Obj a) :
    D.mapLE (hab.trans hbc) x = D.mapLE hbc (D.mapLE hab x) := by
  induction c generalizing a b with
  | zero =>
    obtain rfl := Nat.le_zero.mp hbc
    obtain rfl := Nat.le_zero.mp hab
    rfl
  | succ k ih =>
    by_cases hb : b = k + 1
    · subst hb
      by_cases ha : a = k + 1
      · subst ha
        simp only [D.mapLE, dite_true]; rfl
      · simp only [D.mapLE, dite_true, dif_neg ha, Function.comp_apply]; rfl
    · by_cases ha : a = k + 1
      · omega
      · simp only [D.mapLE, dif_neg ha, dif_neg hb, Function.comp_apply]
        exact congrArg D.step (ih hab (by omega) x)

def D : ℕ ⥤ Type u where
  obj := D.Obj
  map {m n} f := D.mapLE f.down.down
  map_id n := by
    ext x
    simp only [types_id_apply]
    cases n with
    | zero => simp [D.mapLE]
    | succ n => simp [D.mapLE]
  map_comp {a b c} f g := by
    ext x
    simp only [types_comp_apply]
    exact D.mapLE_trans f.down.down g.down.down x

def μN := ℕ
def μN' : Type u := Limits.colimit D

def in' : N.obj μN → μN
  | .inl () => .zero
  | .inr n => n.succ

def out : μN → N.obj μN
  | .zero => .inl ()
  | .succ n => .inr n

def iso : μN ≅ N.obj μN where
  hom := out
  inv := in'
  hom_inv_id := by ext (_ | _) <;> rfl
  inv_hom_id := by ext (_ | _) <;> rfl

variable {α : Type u} {f : Unit ⊕ α → α} {k : ℕ}

def Nat.foldO (zs : Unit ⊕ α → α) : μN → α :=
  Nat.fold' (zs (.inl ())) (zs ∘ .inr)

example : Nat.foldO f Nat.zero = f (.inl ()) := rfl
example : Nat.foldO f (Nat.succ k) = f (.inr (Nat.foldO f k)) := rfl

example : Nat.foldO f (in' (.inl ())) = f (.inl ()) := rfl
example : Nat.foldO f (in' (.inr k)) = f (.inr (Nat.foldO f k)) := rfl

def Nat.foldO_str {α} {f : Unit ⊕ α → α} : Nat.foldO f ∘ in' = f ∘ N.map (Nat.foldO f) := by
  ext (_ | _) <;> rfl

/-! Definition 3.2.1 -/

variable (X Y : Algebra N) (f : X ⟶ Y)
#check Algebra N
#synth Category (Algebra N)
#check X.a
#check X.str
#check Algebra.Hom
#check f.f
#check f.h

def initial : Algebra N where
  a := μN
  str := in'

def initial_isInitial : Limits.IsInitial initial := by
  constructor
  case desc =>
    intro ⟨⟨A, f⟩, _⟩
    exact ⟨Nat.foldO f, Nat.foldO_str.symm⟩
  case fac => simp
  case uniq =>
    -- Suppose that we have another map h
    intro ⟨⟨A, f⟩, _⟩ ⟨h, hh⟩
    simp only [forall_const]
    congr 1
    -- We establish uniqueness by showing that necessarily h = Nat.foldO f
    change h = Nat.foldO f
    -- Observe that because h is an algebra morphism, we know that
    change N.map h ≫ f = initial.str ≫ h at hh
    -- or equivalently
    change f ∘ N.map h = h ∘ initial.str at hh
    -- Because in' and out form an isomorphism
    have : in' ∘ out = id := iso.hom_inv_id
    -- we also know that
    have h₁ :=
      calc f ∘ N.map h ∘ out
        = h ∘ in' ∘ out := congrArg (· ∘ out) hh
      _ = h := by rw [this]; rfl
    -- Similarly
    have h₂ :=
      calc f ∘ N.map (Nat.foldO f) ∘ out
        = Nat.foldO f ∘ in' ∘ out := congrArg (· ∘ out) Nat.foldO_str.symm
      _ = Nat.foldO f := by rw [this]; rfl
    -- Now we show that for all x : μN, we have that h x = Nat.foldO f x
    ext (x : μN)
    show h x = Nat.foldO f x
    -- We first note that x : μN means that there exists an n : ℕ such that x : N.obj^[n] 0
    -- have : ∃ n : ℕ, x = n := ⟨x, rfl⟩
    induction x
    case zero =>
      calc h .zero
          = (f ∘ N.map h ∘ out) .zero := by rw [h₁]
        _ = (f ∘ N.map h) (out .zero) := rfl
        _ = (f ∘ N.map h) (.inl ()) := rfl
        _ = f (N.map h (.inl ())) := rfl
        _ = f (.inl ()) := rfl
        _ = f (N.map (Nat.foldO f) (.inl ())) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (.inl ()) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (out .zero) := rfl
        _ = (f ∘ N.map (Nat.foldO f) ∘ out) .zero := rfl
        _ = Nat.foldO f .zero := rfl
    case succ k ih =>
      calc h (.succ k)
          = (f ∘ N.map h ∘ out) (.succ k) := by rw [h₁]
        _ = (f ∘ N.map h) (out (.succ k)) := rfl
        _ = (f ∘ N.map h) (.inr k) := rfl
        _ = f (N.map h (.inr k)) := rfl
        _ = f (.inr (h k)) := rfl
        _ = f (.inr (Nat.foldO f k)) := by rw [ih]
        _ = f (N.map (Nat.foldO f) (.inr k)) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (.inr k) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (out (.succ k)) := rfl
        _ = (f ∘ N.map (Nat.foldO f) ∘ out) (.succ k) := rfl
        _ = Nat.foldO f (.succ k) := rfl

end Section2

end Section2

section Section3

namespace Section3

variable {α β : Type u}

inductive TreeB : Type u
  | leaf : Bool → TreeB
  | node : TreeB → TreeB → TreeB

inductive TreeF (α : Type u)
  | leaf : Bool → TreeF α
  | node : α → α → TreeF α

def TreeF.map (f : α → β) : TreeF α → TreeF β
  | leaf b => leaf b
  | node l r => node (f l) (f r)

def T : Type u ⥤ Type u where
  obj X := Sum Bool (X × X)
  map f := Sum.map id (Prod.map f f)

def in' : TreeF TreeB → TreeB
  | .leaf b => .leaf b
  | .node l r => .node l r

def out : TreeB → TreeF TreeB
  | .leaf b => .leaf b
  | .node l r => .node l r

def fold1 (f : TreeF α → α) (t : TreeB) : α :=
  match _h : out t with
  | .leaf b => f (.leaf b)
  | .node l r => f (.node (fold1 f l) (fold1 f r))
decreasing_by
  all_goals
    cases t with
    | leaf b' => simp_all [out]
    | node l' r' =>
      obtain ⟨rfl⟩ := _h
      decreasing_tactic

unsafe def fold2 (f : TreeF α → α) : TreeB → α := (out ≫ TreeF.map (fold2 f) ≫ f : TreeB ⟶ α)

end Section3

end Section3

section Section4

inductive PolynomialFunctor where
  | id
  | const (A : Type u)
  | prod (F G : PolynomialFunctor)
  | coprod (F G : PolynomialFunctor)

set_option hygiene false in
notation "〚" F "〛" => PolynomialFunctor.denotation F

def PolynomialFunctor.denotation : PolynomialFunctor → Type u ⥤ Type u
  | id => 𝟭 (Type u)
  | const A => Functor.const (Type u) |>.obj A
  | prod F G => {
      obj X := 〚F〛.obj X × 〚G〛.obj X
      map f := Prod.map (〚F〛.map f) (〚G〛.map f)
      map_id := by
        intro
        simp
        rfl
      map_comp := by
        intros
        simp only [Functor.map_comp]
        rfl
    }
  | coprod F G => {
      obj X := 〚F〛.obj X ⊕ 〚G〛.obj X
      map f := Sum.map (〚F〛.map f) (〚G〛.map f)
      map_id := by
        intro
        simp only [CategoryTheory.Functor.map_id]
        ext (inl | inr)
        · simp only [Sum.map_inl, types_id_apply]
        · simp only [Sum.map_inr, types_id_apply]
      map_comp := by
        intros
        ext
        simp only [Functor.map_comp, types_comp_apply, Sum.map_map]
        rfl
    }

def μ (F : PolynomialFunctor.{u}) :=
  Limits.colimit 〚F〛

/-! Lemma 3.4.2 -/

def PolynomialFunctor.monotone {α β} (F : PolynomialFunctor) (f : α ↪ β) :
    〚F〛.obj α ↪ 〚F〛.obj β where
  toFun := 〚F〛.map f
  inj' := by
    induction F with
    | id => exact f.injective
    | const A => intro x y h; exact h
    | prod F G ihF ihG =>
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      simp only [denotation, Prod.map, Prod.mk.injEq] at h ⊢
      exact ⟨ihF h.1, ihG h.2⟩
    | coprod F G ihF ihG =>
      rintro (a₁ | a₂) (b₁ | b₂) h
      all_goals
        simp only [denotation, reduceCtorEq,
          Sum.map_inl, Sum.map_inr,
          Sum.inl.injEq, Sum.inr.injEq] at h
      · exact congrArg Sum.inl (ihF h)
      · exact congrArg Sum.inr (ihG h)

/-! Lemma 3.4.3 -/

def PolynomialFunctor.iterate_embedding (F : PolynomialFunctor) (n : ℕ) :
    〚F〛.obj^[n] PEmpty ↪ 〚F〛.obj^[n + 1] PEmpty := by
  induction n with
  | zero => exact ⟨PEmpty.elim, fun x => PEmpty.elim x⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.monotone ih

end Section4

section Section5

#check Functor

structure Inductive (F : Type u ⥤ Type u) where
  alg : Algebra F
  isInitial : IsInitial alg

variable {F : Type u ⥤ Type u} (I : Inductive F)

def Inductive.fold {α} (alg : F.obj α → α) : I.alg.a → α :=
  (I.isInitial.to ⟨α, alg⟩).f

def Inductive.into : F.obj I.alg.a → I.alg.a := I.alg.str

def Inductive.out : I.alg.a → F.obj I.alg.a :=
  Algebra.Initial.strInv I.isInitial

end Section5

section Section9

variable {A B X Y : Type u}

/-! Definition 3.9.7 -/

def PolynomialFunctor.ℛ (F : PolynomialFunctor) (R : Rel A B) : Rel (〚F〛.obj A) (〚F〛.obj B) :=
  match F with
  | id => R
  | const A => @Eq A
  | prod F G => fun (x₁, y₁) (x₂, y₂) => F.ℛ R x₁ x₂ ∧ G.ℛ R y₁ y₂
  | coprod F G => fun
    | .inl x, .inl y => F.ℛ R x y
    | .inr x, .inr y => G.ℛ R x y
    | _, _ => False

def Rel.function (R : Rel A X) (S : Rel B Y) : Rel (A → B) (X → Y) :=
  fun f g => ∀ a x, R a x → S (f a) (g x)

infixr:26 " ⇒ " => Rel.function

variable (F : PolynomialFunctor)

/-! Lemma 3.9.8 -/

lemma PolynomialFunctor.preserves_eq {A : Type u} :
    F.ℛ (@Eq A) = @Eq (〚F〛.obj A) := by
  induction F with
  | id => rfl
  | const B => rfl
  | prod F G ihF ihG =>
    dsimp only [ℛ]
    ext ⟨_, _⟩ ⟨_, _⟩
    rw [ihF, ihG, Prod.mk.injEq]
  | coprod F G ihF ihG =>
    dsimp only [ℛ]
    ext (_ | _) (_ | _)
    · rw [ihF, Sum.inl.injEq]
    · simp
    · simp
    · rw [ihG, Sum.inr.injEq]

/-! Lemma 3.9.9 -/

lemma PolynomialFunctor.preserves_function {A B X Y : Type u}
    {R : Rel A X} {S : Rel B Y} {f : A → B} {g : X → Y}
    (h : (R ⇒ S) f g) :
    (F.ℛ R ⇒ F.ℛ S) (〚F〛.map f) (〚F〛.map g) := by
  induction F with
  | id => exact h
  | const C => intro a b hab; exact hab
  | prod F G ihF ihG =>
    intro (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩
    exact ⟨ihF a₁ b₁ h₁, ihG a₂ b₂ h₂⟩
  | coprod F G ihF ihG =>
    rintro (a | a) (b | b) hab <;> try contradiction
    · exact ihF a b hab
    · exact ihG a b hab

end Section9

section Section10

variable {X Y : Type u} [Preorder X] [Preorder Y]

/-! Definition 3.10.1 -/

#check Preorder
#check Preorder.le_refl
#check Preorder.le_trans

def WF_desc (X : Type u) [Preorder X] : Prop :=
  ¬∃ x : ℕ → X, ∀ n, x n > x (n + 1)

def WF_asc (X : Type u) [Preorder X] : Prop :=
  ¬∃ x : ℕ → X, ∀ n, x n < x (n + 1)

/-! Theorem 3.10.2 -/

-- TODO
theorem WF.induction
    (hwf : WF_asc X)
    (P : X → Prop)
    (hP : ∀ x : X, (∀ y < x, P y) → P x) :
    ∀ x : X, P x := by
  sorry

variable {F : PolynomialFunctor}

/-! Lemma 3.10.3 -/

instance PolynomialFunctor.preorder : Preorder (〚F〛.obj X) where
  le := F.ℛ (· ≤ ·)
  le_refl := by
    induction F with
    | id => intro a; exact le_rfl
    | const A => intro a; rfl
    | prod F G ihF ihG =>
      intro (a₁, a₂)
      exact ⟨ihF a₁, ihG a₂⟩
    | coprod F G ihF ihG =>
      rintro (a | a)
      · exact ihF a
      · exact ihG a
  le_trans := by
    induction F with
    | id =>
      intro a b c hab hbc
      exact hab.trans hbc
    | const A =>
      intro a b c hab hbc
      exact hab.trans hbc
    | prod F G ihF ihG =>
      intro (a₁, a₂) (b₁, b₂) (c₁, c₂) ⟨hab₁, hab₂⟩ ⟨hbc₁, hbc₂⟩
      exact ⟨ihF a₁ b₁ c₁ hab₁ hbc₁, ihG a₂ b₂ c₂ hab₂ hbc₂⟩
    | coprod F G ihF ihG =>
      rintro (a | a) (b | b) (c | c) hab hbc <;> try contradiction
      · exact ihF a b c hab hbc
      · exact ihG a b c hab hbc

/-! Lemma 3.10.4 -/

lemma PolynomialFunctor.preserves_monotone (f : X →o Y) : Monotone (〚F〛.map f.toFun) := by
  induction F with
  | id =>
    intro a b hab
    exact f.monotone hab
  | const A =>
    intro a b hab
    exact hab
  | prod F G ihF ihG =>
    intro (a₁, a₂) (b₁, b₂) ⟨hab₁, hab₂⟩
    exact ⟨ihF hab₁, ihG hab₂⟩
  | coprod F G ihF ihG =>
    rintro (a | a) (b | b) hab <;> try contradiction
    · exact ihF hab
    · exact ihG hab

def WF2 (X : Type u) [Preorder X] : Prop :=
  ∀ A : Set X, Inhabited A → ∃ a : A, ∀ b : A, b ≤ a → a ≤ b

theorem iff {X : Type u} [Preorder X] : WF_desc X ↔ WF2 X := by
  apply Iff.intro
  · intro wf A ⟨x⟩
    by_contra h
    replace h : ∀ a : A, ∃ b : A, b < a := by
      intro a
      have ⟨b, hb⟩ := Classical.not_forall.mp (not_exists.mp h a)
      use b
      have ⟨hb₁, hb₂⟩ := Classical.not_imp.mp hb
      exact lt_of_le_not_ge hb₁ hb₂
    let build_chain (n : ℕ) : A := n.recOn x (fun _ prev => (h prev).choose)
    apply wf
    exact ⟨fun n => (build_chain n).1, fun n => (h (build_chain n)).choose_spec⟩
  · intro wf ⟨chain, hchain⟩
    have ⟨⟨min, hmin⟩, hmin_spec⟩ := wf (Set.range chain) ⟨⟨chain 0, Set.mem_range_self 0⟩⟩
    obtain ⟨i, hi⟩ := Set.mem_range.mp hmin
    have : chain (i + 1) ≤ min := hi ▸ (hchain i).le
    exact (hchain i).not_ge (hi.symm ▸ hmin_spec ⟨chain (i + 1), Set.mem_range_self _⟩ this)

end Section10

end Chapter3

section Chapter4

universe u

section Section1

/-! Definition 4.1.1 -/

variable {X : Type u} [inst₁ : SemilatticeSup X] [inst₂ : OrderBot X]
#check SemilatticeSup
#check inst₁.toPartialOrder
#check inst₂.bot
#check inst₂.bot_le
#check sup_le_sup
#check inst₁.le_sup_left
#check inst₁.le_sup_right

variable (α : Type u)
#synth SemilatticeSup (Set α)

#synth SemilatticeSup ℕ

#synth SemilatticeSup Bool

/-! Definition 4.1.2 -/

#check SupBotHom
#check OrderHom

/-! Theorem 4.1.3 -/

theorem semilattice_wfasc_lfp {L : Type u} [SemilatticeSup L] [OrderBot L]
    (hasc : WF_asc L)
    (f : L →o L) :
    ∃ μf : L, Function.IsFixedPt f μf ∧ ∀ x, Function.IsFixedPt f x → μf ≤ x := by
  have incr : ∀ n, f^[n] ⊥ ≤ f^[n + 1] ⊥ :=
    fun n => Monotone.iterate f.monotone n bot_le
  have nsincr : ¬∀ n, f^[n] ⊥ < f^[n + 1] ⊥ := by
    intro h
    exact hasc ⟨fun n => f^[n] ⊥, h⟩
  have ⟨n, hn⟩ : ∃ n, f^[n] ⊥ = f^[n + 1] ⊥ := by
    by_contra h
    push_neg at h
    have : ∀ n, f^[n] ⊥ < f^[n + 1] ⊥ :=
      fun n => lt_of_le_of_ne (incr n) (h n)
    exact nsincr this
  rw [Function.iterate_succ_apply'] at hn
  refine ⟨f^[n] ⊥, hn.symm, ?minimal⟩
  intro x hfix
  have hxconst : ∀ m, f^[m] x = x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      exact hfix
  have : ∀ m, f^[m] ⊥ ≤ f^[m] x :=
    fun m => Monotone.iterate f.monotone m bot_le
  simp only [hxconst] at this
  exact this n

end Section1

section Section2

section Section1

-- TODO transitive closure

end Section1

section Section2

#check ContextFreeGrammar
#check ContextFreeGrammar.NT
#check ContextFreeGrammar.rules

-- TODO string parsing

end Section2

section Section3

-- TODO Dataflow analysis

end Section3

end Section2

section Section3

variable {A B C D : PartOrd}

/-! Definition 4.3.1 -/

namespace PartOrd

def terminal : PartOrd := of PUnit

def terminal.from (X : PartOrd) : X ⟶ terminal :=
  ofHom ⟨fun _ => ⟨⟩, fun _ _ _ => le_rfl⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => ext fun _ => rfl)

def terminalCone : LimitCone (Functor.empty PartOrd) where
  cone := asEmptyCone terminal
  isLimit := isTerminal

def prod (A B : PartOrd.{u}) : PartOrd := of (A × B)

def fst : A.prod B ⟶ A :=
  ofHom ⟨Prod.fst, fun _ _ h => h.1⟩

def snd : A.prod B ⟶ B :=
  ofHom ⟨Prod.snd, fun _ _ h => h.2⟩

def prod_lift (f : C ⟶ A) (g : C ⟶ B) : C ⟶ A.prod B :=
  ofHom {
    toFun x := (f x, g x)
    monotone' _ _ h := ⟨f.hom.monotone h, g.hom.monotone h⟩
  }

def tensor_exchange :
    (A.prod B).prod (C.prod D) ≅ (A.prod C).prod (B.prod D) where
  hom := ofHom {
    toFun := fun ((a, b), (c, d)) => ((a, c), (b, d))
    monotone' := fun _ _ ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ => ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩
  }
  inv := ofHom {
    toFun := fun ((a, c), (b, d)) => ((a, b), (c, d))
    monotone' := fun _ _ ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩ => ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

def prod_isLimit :
    IsLimit (BinaryFan.mk (P := A.prod B) fst snd) :=
  BinaryFan.isLimitMk
    (fun s => prod_lift s.fst s.snd)
    (fun s => rfl)
    (fun s => rfl)
    (fun s m h₁ h₂ => by
      ext x
      apply Prod.ext
      · exact congrArg (·.hom x) h₁
      · exact congrArg (·.hom x) h₂
    )

def binaryProductCone (A B : PartOrd) : LimitCone (pair A B) where
  cone := BinaryFan.mk fst snd
  isLimit := prod_isLimit

instance : CartesianMonoidalCategory PartOrd :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone binaryProductCone

def initial : PartOrd := of PEmpty

def initial.to (X : PartOrd) : initial ⟶ X :=
  ofHom ⟨PEmpty.elim, fun x => x.elim⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => ext fun x => x.elim)

instance : HasInitial PartOrd :=
  IsInitial.hasInitial isInitial

def coprod (A B : PartOrd.{u}) : PartOrd := of (A ⊕ B)

def inl : A ⟶ A.coprod B :=
  ofHom ⟨Sum.inl, fun _ _ => Sum.LiftRel.inl⟩

def inr : B ⟶ A.coprod B :=
  ofHom ⟨Sum.inr, fun _ _ => Sum.LiftRel.inr⟩

def coprod_desc (f : A ⟶ C) (g : B ⟶ C) : A.coprod B ⟶ C :=
  ofHom {
    toFun := Sum.elim f g
    monotone' := by
      rintro (a | b) (a' | b') (hab | hab)
      · exact f.hom.monotone hab
      · exact g.hom.monotone hab
  }

def coprod.isColimit :
    IsColimit (BinaryCofan.mk (P := A.coprod B) PartOrd.inl PartOrd.inr) :=
  BinaryCofan.isColimitMk
    (fun s => coprod_desc s.inl s.inr)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun s m h₁ h₂ => by
      ext (a | b)
      · exact congrArg (·.hom a) h₁
      · exact congrArg (·.hom b) h₂
    )

def dist {A B C : PartOrd.{u}} : A.prod (B.coprod C) ≅ (A.prod B).coprod (A.prod C) where
  hom := ofHom {
    toFun
      | (a, .inl b) => .inl (a, b)
      | (a, .inr c) => .inr (a, c)
    monotone' := by
      rintro ⟨a₁, b₁ | c₁⟩ ⟨a₁, b₂ | c₂⟩ ⟨ha, hb | hc⟩
      · exact Sum.LiftRel.inl ⟨ha, hb⟩
      · exact Sum.LiftRel.inr ⟨ha, hc⟩
  }
  inv := ofHom {
    toFun
      | .inl (a, b) => (a, .inl b)
      | .inr (a, c) => (a, .inr c)
    monotone' := by
      rintro (⟨a₁, b₁⟩ | ⟨a₁, c₁⟩) (⟨a₂, b₂⟩ | ⟨a₂, c₂⟩) (⟨ha, hb⟩ | ⟨ha, hc⟩)
      · exact ⟨ha, Sum.LiftRel.inl hb⟩
      · exact ⟨ha, Sum.LiftRel.inr hc⟩
  }
  hom_inv_id := by ext ⟨a, b | c⟩ <;> rfl
  inv_hom_id := by ext (⟨a, b⟩ | ⟨a, c⟩) <;> rfl

instance (A B : PartOrd) : PartialOrder (A ⟶ B) where
  le f g := ∀ x, f x ≤ g x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ x := (h₁ x).trans (h₂ x)
  le_antisymm f g h₁ h₂ := ext fun x => le_antisymm (h₁ x) (h₂ x)

instance : CartesianMonoidalCategory PartOrd :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone binaryProductCone

def exp (A B : PartOrd) : PartOrd := of (A ⟶ B)

def expFunctor (A : PartOrd) : PartOrd ⥤ PartOrd where
  obj := exp A
  map f := ofHom {
    toFun g := g ≫ f
    monotone' _ _ h x := f.hom.monotone (h x)
  }

def ev : A ⊗ of (A ⟶ B) ⟶ B :=
  ofHom {
    toFun := fun (a, f) => f a
    monotone' := fun (_, f₁) (a₂, _) ⟨ha, hf⟩ =>
      (f₁.hom.monotone ha).trans (hf a₂)
  }

def ev' : of (A ⟶ B) ⊗ A ⟶ B :=
  ofHom {
    toFun := fun (f, a) => f a
    monotone' := fun (f₁, _) (_, a₂) ⟨hf, ha⟩ =>
      (f₁.hom.monotone ha).trans (hf a₂)
  }

def coev : B ⟶ of (A ⟶ A.prod B) :=
  ofHom {
    toFun b := ofHom {
      toFun a := (a, b)
      monotone' _ _ ha := ⟨ha, le_rfl⟩
    }
    monotone' _ _ hb := fun _ => ⟨le_rfl, hb⟩
  }

def tensorProductAdjunction (A : PartOrd.{u}) :
    tensorLeft A ⊣ expFunctor A :=
  Adjunction.mkOfUnitCounit {
    unit.app _ := coev
    counit.app _ := ev
  }

def curry (f : A ⊗ B ⟶ C) : B ⟶ of (A ⟶ C) :=
  ofHom {
    toFun b := ofHom {
      toFun a := f (a, b)
      monotone' := fun _ _ ha => f.hom.monotone ⟨ha, le_rfl⟩
    }
    monotone' := fun _ _ hb _ => f.hom.monotone ⟨le_rfl, hb⟩
  }

def curry_left (f : A ⊗ B ⟶ C) : A ⟶ of (B ⟶ C) :=
  ofHom {
    toFun a := ofHom {
      toFun b := f (a, b)
      monotone' := fun _ _ hb => f.hom.monotone ⟨le_rfl, hb⟩
    }
    monotone' := fun _ _ ha _ => f.hom.monotone ⟨ha, le_rfl⟩
  }

def uncurry (f : B ⟶ of (A ⟶ C)) : A ⊗ B ⟶ C :=
  ofHom {
    toFun := fun (a, b) => f b a
    monotone' := fun (_, b₁) (a₂, _) ⟨ha, hb⟩ =>
      ((f b₁).hom.monotone ha).trans (f.hom.monotone hb a₂)
  }

instance : MonoidalClosed PartOrd :=
  MonoidalClosed.mk fun A => Closed.mk _ (PartOrd.tensorProductAdjunction A)

def disc (X : PartOrd) : PartOrd where
  carrier := X
  str.le := Eq
  str.lt a b := a = b ∧ b ≠ a
  str.le_refl := Eq.refl
  str.le_trans _ _ _ := Eq.trans
  str.le_antisymm _ _ h _ := h

namespace disc

notation "[" X "]ᵈ" => disc X

def comonad : Comonad PartOrd where
  obj := disc
  map {X Y} f :=
    @ofHom [X]ᵈ [Y]ᵈ _ _ ⟨f, fun _ _ => congrArg f⟩
  ε.app X := @ofHom [X]ᵈ X _ _ ⟨id, fun _ _ h => by subst h; exact le_rfl⟩
  δ.app X := @ofHom [X]ᵈ [[X]ᵈ]ᵈ _ _ ⟨id, fun _ _ h => h⟩

notation "[" f "]ᵈ" => disc.comonad.map f

def iso_terminal : [terminal]ᵈ ≅ terminal where
  hom := @ofHom [terminal]ᵈ terminal _ _ ⟨id, fun _ _ _ => le_rfl⟩
  inv := @ofHom terminal [terminal]ᵈ _ _ ⟨id, fun _ _ _ => rfl⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

def iso_prod (X Y : PartOrd) : [X.prod Y]ᵈ ≅ ([X]ᵈ.prod [Y]ᵈ) where
  hom := @ofHom [X.prod Y]ᵈ ([X]ᵈ.prod [Y]ᵈ) _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mp h)⟩
  inv := @ofHom ([X]ᵈ.prod [Y]ᵈ) [X.prod Y]ᵈ _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mpr h)⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end disc

def powerset : PartOrd ⥤ SemilatSupCat where
  obj X := SemilatSupCat.of (Set X)
  map {X Y} f := {
    toFun s := f '' s
    map_sup' := Set.image_union f
    map_bot' := Set.image_empty f
  }
  map_id X := by
    apply SupBotHom.ext
    intro s
    change 𝟙 X '' s = s
    simp
  map_comp {X Y Z} f g := by
    apply SupBotHom.ext
    intro s
    change (f ≫ g) '' s = g '' (f '' s)
    simp [Set.image_image]

def U := forget₂ SemilatSupCat PartOrd

def U.bot (L : SemilatSupCat) : PartOrd.terminal ⟶ U.obj L :=
  PartOrd.ofHom ⟨fun _ => ⊥, fun _ _ _ => le_rfl⟩

def U.sup (L : SemilatSupCat) : (U.obj L).prod (U.obj L) ⟶ U.obj L :=
  PartOrd.ofHom ⟨fun (x, y) => x ⊔ y, fun _ _ ⟨hx, hy⟩ => sup_le_sup hx hy⟩

def one {X : PartOrd} : [X]ᵈ ⟶ U.obj (powerset.obj X) :=
  PartOrd.ofHom (X := [X]ᵈ) {
    toFun x := ({x} : Set X)
    monotone' := by intro _ _ rfl; rfl
  }

end PartOrd

end Section3

section Section4

namespace STLC

inductive FinTy : Type u
  | unit
  | prod (T₁ T₂ : FinTy)
  | coprod (T₁ T₂ : FinTy)
  | powerset (T : FinTy)
  | discrete (T : FinTy)

inductive Ty : Type u
  | unit
  | prod (A B : Ty)
  | arr (A B : Ty)
  | coprod (A B : Ty)
  | powerset (T : FinTy)
  | discrete (A : Ty)

inductive LatTy : Type u
  | unit
  | prod (L₁ L₂ : LatTy)
  | powerset (T : FinTy)

inductive Tm : Type u
  | var (x : ℕ)
  | abs (A : Ty) (e : Tm)
  | app (e₁ e₂ : Tm)
  | unit
  | prod (e₁ e₂ : Tm)
  | fst (e : Tm)
  | snd (e : Tm)
  | inl (e : Tm)
  | inr (e : Tm)
  | case (e e₁ e₂ : Tm)
  | bot (L : LatTy)
  | sup (L : LatTy) (e₁ e₂ : Tm)
  | for (e₁ e₂ : Tm)
  | one (e : Tm)
  | discrete (e : Tm)
  | discrete_elim (e₁ e₂ : Tm)
  | fix (L : LatTy) (e : Tm)

inductive Qualifier
  | D
  | none

abbrev Ctx := List (Qualifier × Ty)

def Ctx.disc : Ctx → Ctx :=
  List.filter (· matches (.D, _))

instance : One Ty := ⟨Ty.unit⟩
instance : One FinTy := ⟨FinTy.unit⟩
instance : One LatTy := ⟨LatTy.unit⟩
notation "[" A "]ᵈ" => Ty.discrete A
notation "[" T "]ᵈ" => FinTy.discrete T
prefix:100 "𝒫 " => Ty.powerset

def FinTy.toTy : FinTy → Ty
  | .unit => .unit
  | .prod T₁ T₂ => .prod T₁.toTy T₂.toTy
  | .coprod T₁ T₂ => .coprod T₁.toTy T₂.toTy
  | .powerset T => .powerset T
  | .discrete T => .discrete T.toTy

def LatTy.toTy : LatTy → Ty
  | .unit => .unit
  | .prod L₁ L₂ => .prod L₁.toTy L₂.toTy
  | .powerset T => .powerset T

instance : Coe LatTy Ty := ⟨LatTy.toTy⟩

notation "π₁" => Tm.fst
notation "π₂" => Tm.snd
notation "ι₁" => Tm.inl
notation "ι₂" => Tm.inr
instance : Singleton Tm Tm := ⟨Tm.one⟩
notation "[" e "]ᵈ" => Tm.discrete e

notation "[" Γ "]ᵈ" => Ctx.disc Γ

set_option hygiene false in
notation:max Γ " ⊢ " e " : " A => HasType Γ e A

inductive HasType : Ctx → Tm → Ty → Type u
  | var {Γ} x A :
    (Γ[x]? = some (.none, A)) →
    (Γ ⊢ .var x : A)
  | dvar {Γ} x A :
    (Γ[x]? = some (.D, A)) →
    (Γ ⊢ .var x : A)
  | unit_intro {Γ} :
    (Γ ⊢ .unit : 1)
  | prod_intro {Γ} e₁ e₂ A₁ A₂ :
    (Γ ⊢ e₁ : A₁) →
    (Γ ⊢ e₂ : A₂) →
    (Γ ⊢ e₁.prod e₂ : A₁.prod A₂)
  | prod_elim₁ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₁.prod A₂) →
    (Γ ⊢ π₁ e : A₁)
  | prod_elim₂ {Γ} e (A₁ A₂ : Ty) :
    (Γ ⊢ e : A₁.prod A₂) →
    (Γ ⊢ π₂ e : A₂)
  | abs_intro {Γ} e A B :
    (((.none, A) :: Γ) ⊢ e : B) →
    (Γ ⊢ .abs A e : .arr A B)
  | abs_elim {Γ} e₁ e₂ A B :
    (Γ ⊢ e₁ : .arr A B) →
    (Γ ⊢ e₂ : A) →
    (Γ ⊢ e₁.app e₂ : B)
  | coprod_intro₁ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₁) →
    (Γ ⊢ ι₁ e : .coprod A₁ A₂)
  | coprod_intro₂ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₂) →
    (Γ ⊢ ι₂ e : .coprod A₁ A₂)
  | coprod_elim {Γ} e e₁ e₂ A₁ A₂ C :
    (Γ ⊢ e : .coprod A₁ A₂) →
    (((.none, A₁) :: Γ) ⊢ e₁ : C) →
    (((.none, A₂) :: Γ) ⊢ e₂ : C) →
    (Γ ⊢ .case e e₁ e₂ : C)
  | discrete_intro {Γ} e A :
    ([Γ]ᵈ ⊢ e : A) →
    (Γ ⊢ [e]ᵈ : [A]ᵈ)
  | discrete_elim {Γ} e₁ e₂ A C :
    (Γ ⊢ e₁ : [A]ᵈ) →
    (((.D, A) :: Γ) ⊢ e₂ : C) →
    (Γ ⊢ .discrete_elim e₁ e₂ : C)
  | bot_intro {Γ} L :
    (Γ ⊢ .bot L : L)
  | one_intro {Γ} e (T : FinTy) :
    ([Γ]ᵈ ⊢ e : T.toTy) →
    (Γ ⊢ {e} : 𝒫 T)
  | sup_intro {Γ} e₁ e₂ (L : LatTy) :
    (Γ ⊢ e₁ : L) →
    (Γ ⊢ e₂ : L) →
    (Γ ⊢ .sup L e₁ e₂ : L)
  | for_intro {Γ} e₁ e₂ (T : FinTy) (L : LatTy) :
    (Γ ⊢ e₁ : 𝒫 T) →
    (((.D, T.toTy) :: Γ) ⊢ e₂ : L) →
    (Γ ⊢ .for e₁ e₂ : L)
  | fix_intro {Γ} e (L : LatTy) :
    (((.none, L) :: [Γ]ᵈ) ⊢ e : L) →
    (Γ ⊢ .fix L e : L)

open PartOrd

set_option hygiene false in
notation "〚" A "〛" => FinTy.denotation A

def FinTy.denotation : FinTy.{u} → PartOrd.{u}
  | 1 => 𝟙_ PartOrd
  | prod T₁ T₂ => 〚T₁〛 ⊗ 〚T₂〛
  | coprod T₁ T₂ => 〚T₁〛.coprod 〚T₂〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛)
  | discrete T => [〚T〛]ᵈ

set_option hygiene false in
notation "〚" A "〛" => Ty.denotation A

def Ty.denotation : Ty.{u} → PartOrd.{u}
  | 1 => PartOrd.terminal
  | prod A B => 〚A〛 ⊗ 〚B〛
  | arr A B => 〚A〛.exp 〚B〛
  | coprod A B => 〚A〛.coprod 〚B〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛)
  | discrete A => [〚A〛]ᵈ

lemma FinTy.toTy_denotation {T : FinTy} : 〚T〛 = 〚T.toTy〛 := by
  induction T with
  | unit => rfl
  | prod T₁ T₂ ihT₁ ihT₂ =>
    dsimp [FinTy.denotation]
    rw [ihT₁, ihT₂]
    rfl
  | coprod T₁ T₂ ihT₁ ihT₂ =>
    dsimp [FinTy.denotation]
    rw [ihT₁, ihT₂]
    rfl
  | powerset T => rfl
  | discrete T ihT =>
    dsimp [FinTy.denotation]
    rw [ihT]
    rfl

def LatTy.denotation : LatTy.{u} → CompleteLat.{u}
  | .unit => CompleteLat.of PUnit
  | .prod L₁ L₂ => CompleteLat.of (L₁.denotation × L₂.denotation)
  | .powerset T => CompleteLat.of (Set 〚T〛)

instance : HasForget₂ CompleteLat PartOrd where
  forget₂.obj L := PartOrd.of L
  forget₂.map f := PartOrd.ofHom ⟨f, f.toBoundedLatticeHom.toBoundedOrderHom.toOrderHom.monotone⟩

lemma LatTy.toTy_denotation {L : LatTy} :
    (forget₂ CompleteLat PartOrd).obj L.denotation = 〚L〛 := by
  induction L with
  | unit => rfl
  | prod L₁ L₂ ihL₁ ihL₂ =>
    dsimp [LatTy.denotation, LatTy.toTy, Ty.denotation]
    rw [← ihL₁, ← ihL₂]
    rfl
  | powerset => rfl

instance LatTy.instCompleteLattice (L : LatTy) : CompleteLattice 〚L〛 := by
  rw [← toTy_denotation]
  dsimp only [forget₂, HasForget₂.forget₂]
  infer_instance

def LatTy.bot (L : LatTy) : PartOrd.terminal ⟶ 〚L〛 :=
  ofHom ⟨fun ⟨⟩ => ⊥, fun ⟨⟩ ⟨⟩ ⟨⟩ => le_rfl⟩

def LatTy.sup : ∀ L : LatTy, 〚L〛 ⊗ 〚L〛 ⟶ 〚L〛
  | .unit => terminal.from _
  | .prod L₁ L₂ => tensor_exchange.hom ≫ (sup L₁ ⊗ₘ sup L₂)
  | .powerset T => U.sup (PartOrd.powerset.obj 〚T〛)

def LatTy.comprehension {A : PartOrd} {X : FinTy} (L : LatTy) (f : A ⊗ [〚X〛]ᵈ ⟶ 〚L〛) :
    A ⊗ 〚𝒫 X〛 ⟶ 〚L〛 :=
  PartOrd.ofHom {
    toFun := fun (a, (s : Set 〚X〛)) => ⨆ x ∈ s, f (a, x)
    monotone' := by
      intro (a₁, s₁) (a₂, s₂) ⟨ha, hs⟩
      simp_all [Ty.denotation]
      change Set 〚X〛 at s₁ s₂
      have := iSup_le_iSup_of_subset (f := fun x : [〚X〛]ᵈ => f (a₁, x)) hs
      dsimp only at this
      simp only [iSup_le_iff] at this
      have := iSup₂_le (f := fun (x : 〚X〛) (_ : x ∈ s₁) => f (a₁, x))
        (a := ⨆ x ∈ s₂, f (a₂, x))
      have : ∀ x ∈ s₁, f (a₁, x) ≤ ⨆ x ∈ s₂, f (a₂, x) := by
        intro x hx
        have := f.hom.monotone
        unfold Monotone Hom.hom at this
        have hx₂ : x ∈ s₂ := hs hx
        have h := @this (a₁, x) (a₂, x) ⟨ha, le_rfl⟩
        trans
        · exact h
        · have := le_iSup₂ (f := fun (x : 〚X〛) (_ : x ∈ s₂) => f (a₂, x)) x hx₂
          convert this
          have ca : 〚L〛 = (forget₂ CompleteLat PartOrd).obj L.denotation :=
            (LatTy.toTy_denotation (L := L)).symm
          change 〚L〛.str = L.instCompleteLattice.toCompleteSemilatticeInf.toPartialOrder
          sorry
      sorry
  }

def LatTy.fix {A : PartOrd} {L : LatTy} (f : [A]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) :
    [A]ᵈ ⟶ 〚L〛 :=
  @PartOrd.ofHom [A]ᵈ 〚L〛 _ _ {
    toFun a := sorry
    monotone' _ _ ha := by subst ha; rfl
  }

set_option hygiene false in
notation "〚" Γ "〛" => Ctx.denotation Γ

def Ctx.denotation : Ctx.{u} → PartOrd.{u}
  | [] => 𝟙_ PartOrd
  | (.none, A) :: Γ => 〚Γ〛 ⊗ 〚A〛
  | (.D, A) :: Γ => 〚Γ〛 ⊗ [〚A〛]ᵈ

def Ctx.lookup {q A} : (Γ : Ctx) → (x : ℕ) → Γ[x]? = some (q, A) → (〚Γ〛 ⟶ 〚A〛)
  | (.none, A) :: Γ, 0, rfl => snd
  | (.none, _) :: Γ, x + 1, h => fst ≫ Ctx.lookup Γ x h
  | (.D, A) :: Γ, 0, rfl => snd ≫ disc.comonad.ε.app 〚A〛
  | (.D, _) :: Γ, x + 1, h => fst ≫ Ctx.lookup Γ x h

def Ctx.drop (Γ : Ctx) : 〚Γ〛 ⟶ 〚[Γ]ᵈ〛 :=
  match Γ with
  | [] => 𝟙 〚[]〛
  | (.none, _) :: Γ => fst ≫ Ctx.drop Γ
  | (.D, A) :: Γ => Ctx.drop Γ ⊗ₘ 𝟙 [〚A〛]ᵈ

lemma Ctx.disc.idem {Γ : Ctx} : [[Γ]ᵈ]ᵈ = [Γ]ᵈ := by
  let p : Qualifier × Ty → Bool := (· matches (.D, _))
  have := @List.filter_filter _ p p Γ
  simp [Ctx.disc]

def Ctx.δ (Δ : Ctx) (h : [Δ]ᵈ = Δ := by exact Ctx.disc.idem) : 〚Δ〛 ⟶ [〚Δ〛]ᵈ :=
  match Δ with
  | [] => disc.iso_terminal.inv
  | (.D, A) :: Δ =>
    (Ctx.δ Δ (congrArg List.tail h) ⊗ₘ disc.comonad.δ.app 〚A〛) ≫ (disc.iso_prod 〚Δ〛 [〚A〛]ᵈ).inv
  | (.none, _) :: Δ => by simpa using List.filter_eq_self.mp h

set_option hygiene false in
notation "〚" h "〛" => HasType.denotation h

open Ctx (drop δ) in
def HasType.denotation {Γ e A} : (Γ ⊢ e : A) → (〚Γ〛 ⟶ 〚A〛)
  | var x A hx => Ctx.lookup Γ x hx
  | dvar x A hx => Ctx.lookup Γ x hx
  | unit_intro => terminal.from 〚Γ〛
  | prod_intro e₁ e₂ A₁ A₂ he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : A₁ from he₁〛
    let g := 〚show Γ ⊢ e₂ : A₂ from he₂〛
    prod_lift f 〚he₂〛
  | prod_elim₁ e A₁ A₂ he => 〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ fst
  | prod_elim₂ e A₁ A₂ he => 〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ snd
  | abs_intro e A B he => curry_left 〚show ((.none, A) :: Γ) ⊢ e : B from he〛
  | abs_elim e₁ e₂ A B he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : A.arr B from he₁〛
    let g := 〚show Γ ⊢ e₂ : A from he₂〛
    prod_lift f g ≫ ev'
  | coprod_intro₁ e A₁ A₂ he => 〚show Γ ⊢ e : A₁ from he〛 ≫ inl
  | coprod_intro₂ e A₁ A₂ he => 〚show Γ ⊢ e : A₂ from he〛 ≫ inr
  | coprod_elim e e₁ e₂ A₁ A₂ C he he₁ he₂ =>
    let f := 〚show Γ ⊢ e : A₁.coprod A₂ from he〛
    let g₁ := 〚show ((.none, A₁) :: Γ) ⊢ e₁ : C from he₁〛
    let g₂ := 〚show ((.none, A₂) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ dist.hom ≫ coprod_desc g₁ g₂
  | discrete_intro e A he => drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : A from he〛]ᵈ
  | discrete_elim e₁ e₂ A C he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : [A]ᵈ from he₁〛
    let g := 〚show ((.D, A) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ g
  | bot_intro L => PartOrd.terminal.from 〚Γ〛 ≫ LatTy.bot L
  | one_intro e T he =>
    drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : T.toTy from he〛]ᵈ ≫ (FinTy.toTy_denotation ▸ one)
  | sup_intro e₁ e₂ L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : L from he₁〛
    let g := 〚show Γ ⊢ e₂ : L from he₂〛
    prod_lift f g ≫ LatTy.sup L
  | for_intro e₁ e₂ T L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : 𝒫 T from he₁〛
    let g := 〚show ((.D, T.toTy) :: Γ) ⊢ e₂ : L from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ LatTy.comprehension L (FinTy.toTy_denotation ▸ g)
  | fix_intro e L he =>
    let f := 〚show ((.none, L) :: [Γ]ᵈ) ⊢ e : L from he〛
    drop Γ ≫ δ [Γ]ᵈ ≫ LatTy.fix ((disc.comonad.ε.app 〚[Γ]ᵈ〛 ⊗ₘ 𝟙 〚L〛) ≫ f)

end STLC

end Section4

section Section5

-- TODO Incrementalizing fixed point algorithms

end Section5

section Section6

section Section1

/-! Definition 4.6.1 -/

structure Change where
  X : PartOrd.{u}
  Δ : PartOrd.{u}
  V : SetRel X Δ
  update : V → X
  update_monotone : ∀ xdx : V, xdx.1.1 ≤ update xdx
  zero : X → Δ
  zero_valid : ∀ x, (x, zero x) ∈ V
  zero_update: ∀ x, update ⟨(x, zero x), zero_valid x⟩ = x

notation x " ⨁[" 𝕏 "]" dx => Change.update 𝕏 ⟨(x, dx), by aesop⟩
notation "𝟬[" 𝕏 "]" => Change.zero 𝕏

/-! Example 4.6.2 -/

example : Change where
  X := PartOrd.of (Fin 100)
  Δ := PartOrd.of ℕ
  V := {(n, k) : Fin 100 × ℕ | n + k < 100}
  update := fun ⟨(n, k), h⟩ => ⟨n + k, by rw [Set.mem_setOf_eq] at h; omega⟩
  update_monotone := by
    simp only [Subtype.forall, Prod.forall]
    intro ⟨n, hn⟩ k h
    simp
  zero x := 0
  zero_valid := Fin.isLt
  zero_update _ := rfl

/-! Example 4.6.3 -/

def Change.ofCompleteLat (L : CompleteLat) : Change where
  X := PartOrd.of L
  Δ := PartOrd.of L
  V := Set.univ
  update := fun ⟨(x, dx), ⟨⟩⟩ => x ⊔ dx
  update_monotone _ := le_sup_left
  zero _ := ⊥
  zero_valid := Set.mem_univ
  zero_update := sup_bot_eq

end Section1

section Section2

/-! Definition 4.6.4 -/

/--
Helper structure to define derivatives
Dependently typed, as `eq` depends on `hy`
-/
structure Deriv {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ)
    x dx
    (_ : (x, dx) ∈ 𝕏.V) : Prop where
  hy : (f x, f' (x, dx)) ∈ 𝕐.V
  eq : f (x ⨁[𝕏] dx) = f x ⨁[𝕐] f' (x, dx)

def IsDerivative {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) : Prop :=
  ∀ x dx, (hx : (x, dx) ∈ 𝕏.V) → Deriv f f' x dx hx

section

notation "𝒫ℕ'" => Change.ofCompleteLat (CompleteLat.of (Set ℕ))
notation "𝒫ℕ" => PartOrd.of (Set ℕ)

def f : 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun X := X ∪ {1, 2}
    monotone' {X Y} h := by
      simp only [Set.union_insert, Set.union_singleton]
      apply Set.insert_subset_insert
      apply Set.insert_subset_insert
      exact h
  }

def f'₀ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx
    monotone' _ _ | ⟨_, hdx⟩ => hdx
  }

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₀ := by
  intro x dx h
  constructor
  · sorry
  · sorry

def f'₁ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {1}
    monotone' := by
      intro (x, y) (dx, dy) ⟨hdx, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

def f'₂ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {2}
    monotone' := by
      intro (x, y) (dx, dy) ⟨hdx, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

def f'₃ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {1, 2}
    monotone' := by
      intro (x, y) (dx, dy) ⟨_, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

end

/-! Definition 4.6.5 -/

namespace SeminaiveFP

variable (L : CompleteLat.{u})
  (f : PartOrd.of L ⟶ PartOrd.of L)
  (f' : [PartOrd.of L]ᵈ ⊗ PartOrd.of L ⟶ PartOrd.of L)

mutual

def x : ℕ → PartOrd.of L
  | 0 => ⊥
  | i + 1 => x i ⊔ dx i

def dx : ℕ → PartOrd.of L
  | 0 => f ⊥
  | i + 1 => f' (x i, dx i)

end

def semifix
    (_ : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') : L :=
  ⨆ i, x L f f' i

/-! Theorem 4.6.6 -/

theorem semifix_fix
    (hasc : WF_asc L)
    (der : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') :
    semifix L f f' der = f.hom.lfp := by
  let x := x L f f'
  let dx := dx L f f'
  have : ∀ i, x (i + 1) = f (x i) := by
    intro i
    induction i with
    | zero =>
      calc x 1
          = x 0 ⊔ dx 0 := rfl
        _ = ⊥ ⊔ f ⊥ := rfl
        _ = f ⊥ := bot_sup_eq (f ⊥)
        _ = f (x 0) := rfl
    | succ j ih =>
      calc x (j + 2)
          = x (j + 1) ⊔ dx (j + 1) := rfl
        _ = f (x j) ⊔ dx (j + 1) := by rw [ih]
        _ = f (x j) ⊔ f' (x j, dx j) := rfl
        _ = f (x j ⊔ dx j) := der (x j) (dx j) ⟨⟩ |>.2.symm
        _ = f (x (j + 1)) := rfl
  have h : ∀ i, x i = f^[i] ⊥ := by
    intro i
    induction i with
    | zero => rfl
    | succ j ih =>
      rw [this, Function.iterate_succ_apply' f j ⊥, ih]
  have := fixedPoints.lfp_eq_sSup_iterate f.hom
  symm
  change f.hom.lfp = ⨆ i, x i
  simp only [h]
  change f.hom.lfp = ⨆ i, f^[i] ⊥
  apply this
  sorry

end SeminaiveFP

end Section2

namespace Change

section Section3

variable (𝕏 𝕐 : Change)

def Hom.Base : Type u :=
  {(f, f') : (𝕏.X ⟶ 𝕐.X) × ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) | IsDerivative f f'}

def Hom.Rel : Setoid (Base 𝕏 𝕐) where
  r | ⟨(f, _), _⟩, ⟨(g, _), _⟩ => f = g
  iseqv.refl _ := rfl
  iseqv.symm := Eq.symm
  iseqv.trans := Eq.trans

def Hom.Quot := Quotient (Hom.Rel 𝕏 𝕐)

@[ext]
structure Hom where
  base : 𝕏.X ⟶ 𝕐.X
  hasDeriv : ∃ f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ, IsDerivative base f'

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective' _ _ h :=
    Hom.ext (ConcreteCategory.hom_injective (DFunLike.coe_fn_eq.mp h))

variable {𝕏 𝕐 : Change}

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) : ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) :=
  h.hasDeriv.choose

def id 𝕏 : Hom 𝕏 𝕏 where
  base := 𝟙 𝕏.X
  hasDeriv := ⟨PartOrd.ofHom ⟨fun (_, dx) => dx, fun _ _ ⟨_, h⟩ => h⟩, fun _ _ hx => ⟨hx, rfl⟩⟩

end Section3

instance : LargeCategory Change where
  Hom := Hom
  id := id
  comp {𝕏 𝕐 𝕫} f g := {
    base := f.base ≫ g.base
    hasDeriv := by
      obtain ⟨f, f', hf⟩ := f
      obtain ⟨g, g', hg⟩ := g
      refine ⟨?_, ?_⟩
      · refine PartOrd.ofHom ⟨fun (x, dx) => g' (f x, f' (x, dx)), ?_⟩
        intro (x₁, dx₁) (x₂, dx₂) ⟨h₁, h₂⟩
        change g' (f x₁, f' (x₁, dx₁)) ≤ g' (f x₂, f' (x₂, dx₂))
        refine g'.hom.monotone ⟨?_, ?_⟩
        · change f x₁ = f x₂
          exact congrArg f h₁
        · change f' (x₁, dx₁) ≤ f' (x₂, dx₂)
          exact f'.hom.monotone ⟨h₁, h₂⟩
      · intro x dx hx
        have ⟨hy, hf⟩ := hf x dx hx
        have ⟨hz, hg⟩ := hg (f x) (f' (x, dx)) hy
        refine ⟨hz, ?_⟩
        calc g (f (x ⨁[𝕏] dx))
            = g (f x ⨁[𝕐] f' (x, dx)) := congrArg g hf
          _ = g (f x) ⨁[𝕫] g' (f x, f' (x, dx)) := hg
  }

section Section4

/-! Definition 4.6.7 -/

def terminal : Change where
  X := PartOrd.terminal
  Δ := PartOrd.terminal
  V := Set.univ
  update _ := ⟨⟩
  update_monotone _ := le_rfl
  zero _ := ⟨⟩
  zero_valid := Set.mem_univ
  zero_update _ := rfl

def terminal.from (𝕏 : Change) : 𝕏 ⟶ terminal where
  base := PartOrd.terminal.from 𝕏.X
  hasDeriv := ⟨PartOrd.terminal.from ([𝕏.X]ᵈ ⊗ 𝕏.Δ), fun _ _ _ => ⟨⟨⟩, rfl⟩⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => rfl)

end Section4

def initial : Change where
  X := PartOrd.initial
  Δ := PartOrd.initial
  V := Set.univ
  update _ := _
  update_monotone _ := le_rfl
  zero := PEmpty.elim
  zero_valid := Set.mem_univ
  zero_update _ := rfl

def initial.to (𝕏 : Change) : initial ⟶ 𝕏 where
  base := PartOrd.initial.to 𝕏.X
  hasDeriv := ⟨PartOrd.ofHom ⟨fun (_, dx) => dx.elim, fun (_, dx₁) => dx₁.elim⟩, fun x => x.elim⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => Hom.ext <| PartOrd.ext fun x => x.elim)

section Section5

/-! Definition 4.6.8 -/

def prod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X ⊗ 𝕐.X
  Δ := 𝕏.Δ ⊗ 𝕐.Δ
  V := {((x, y), (dx, dy)) | (x, dx) ∈ 𝕏.V ∧ (y, dy) ∈ 𝕐.V}
  update := fun ⟨((x, y), (dx, dy)), ⟨hx, hy⟩⟩ =>
    (x ⨁[𝕏] dx, y ⨁[𝕐] dy)
  update_monotone := fun ⟨((x, y), (dx, dy)), ⟨hx, hy⟩⟩ =>
    ⟨𝕏.update_monotone ⟨(x, dx), hx⟩, 𝕐.update_monotone ⟨(y, dy), hy⟩⟩
  zero | (x, y) => (𝟬[𝕏] x, 𝟬[𝕐] y)
  zero_valid | (x, y) => ⟨𝕏.zero_valid x, 𝕐.zero_valid y⟩
  zero_update | (x, y) => Prod.ext (𝕏.zero_update x) (𝕐.zero_update y)

end Section5

section Section6

/-! Definition 4.6.9 -/

def coprod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X.coprod 𝕐.X
  Δ := 𝕏.Δ.coprod 𝕐.Δ
  V := { (xy, dxy) |
    match xy, dxy with
    | .inl x, .inl dx => (x, dx) ∈ 𝕏.V
    | .inr y, .inr dy => (y, dy) ∈ 𝕐.V
    | _, _ => False }
  update
    | ⟨(.inl x, .inl dx), h⟩ => .inl (x ⨁[𝕏] dx)
    | ⟨(.inr y, .inr dy), h⟩ => .inr (y ⨁[𝕐] dy)
  update_monotone
    | ⟨(.inl x, .inl dx), h⟩ =>
      Sum.inl_le_inl_iff.mpr (𝕏.update_monotone ⟨(x, dx), h⟩)
    | ⟨(.inr y, .inr dy), h⟩ =>
      Sum.inr_le_inr_iff.mpr (𝕐.update_monotone ⟨(y, dy), h⟩)
  zero
    | .inl x => .inl (𝟬[𝕏] x)
    | .inr y => .inr (𝟬[𝕐] y)
  zero_valid
    | .inl x => 𝕏.zero_valid x
    | .inr y => 𝕐.zero_valid y
  zero_update
    | .inl x => congrArg Sum.inl (𝕏.zero_update x)
    | .inr y => congrArg Sum.inr (𝕐.zero_update y)

end Section6

section Section7

instance {𝕏 𝕐 : Change} : PartialOrder (𝕏 ⟶ 𝕐) := sorry

noncomputable def exp (𝕏 𝕐 : Change) : Change where
  X := PartOrd.of (𝕏 ⟶ 𝕐)
  Δ := PartOrd.of ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ)
  V := { (f, df) : (𝕏 ⟶ 𝕐) × ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) |
      ∃ g' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ, ∀ x dx,
        (_ : (x, dx) ∈ 𝕏.V) →
        -- TODO make this a dependent sum
        (_ : (f.base x, df (x, dx)) ∈ 𝕐.V) →
        (_ : (f.base (x ⨁[𝕏] dx), df (x ⨁[𝕏] dx, 𝟬[𝕏] (x ⨁[𝕏] dx))) ∈ 𝕐.V) →
        (_ : (f.base x, df (x, 𝟬[𝕏] x)) ∈ 𝕐.V) →
        (_ : (f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x), g' (x, dx)) ∈ 𝕐.V) →
        ((f.base x ⨁[𝕐] df (x, dx)) = f.base (x ⨁[𝕏] dx) ⨁[𝕐] df (x ⨁[𝕏] dx, 𝟬[𝕏] (x ⨁[𝕏] dx))) ∧
        ((f.base x ⨁[𝕐] df (x, dx)) = (f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x)) ⨁[𝕐] g' (x, dx))
      }
  update
    | ⟨(f, df), h⟩ => sorry -- fun x => f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x)
  update_monotone
    | ⟨(f, df), h⟩ => sorry
  zero f := f.hasDeriv.choose
  zero_valid := by
    intro ⟨f, f', hf⟩
    simp
    sorry
  zero_update := by
    intro ⟨f, f', hf⟩
    simp
    sorry

end Section7

section Section8

def disc (𝕏 : Change) : Change where
  X := [𝕏.X]ᵈ
  Δ := 𝟙_ PartOrd
  V := Set.univ
  update | ⟨(x, ⟨⟩), ⟨⟩⟩ => x
  update_monotone _ := rfl
  zero _ := ⟨⟩
  zero_valid := Set.mem_univ
  zero_update _ := rfl

namespace disc

notation "[" 𝕏 "]ᵈ" => disc 𝕏

def functor : Comonad Change where
  obj := disc
  map {𝕏 𝕐} f := {
    base := @PartOrd.ofHom [𝕏]ᵈ.X [𝕐]ᵈ.X _ _ {
      toFun := f.base
      monotone' a b := congrArg f.base
    }
    hasDeriv :=
      ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => ⟨⟩, fun _ _ _ => le_rfl⟩, fun x dx hx => ⟨hx, rfl⟩⟩
  }
  ε.app 𝕏 := {
    base := @PartOrd.ofHom [𝕏]ᵈ.X 𝕏.X _ _
      ⟨fun x => x, fun a b hab => by rw [hab]⟩
    hasDeriv := by
      refine ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => 𝟬[𝕏] x, ?_⟩, ?_⟩
      · rintro ⟨x₁, ⟨⟩⟩ ⟨x₂, ⟨⟩⟩ ⟨rfl, ⟨⟩⟩
        rfl
      · intro x ⟨⟩ ⟨⟩
        exact ⟨𝕏.zero_valid x, 𝕏.zero_update x |>.symm⟩
  }
  δ.app 𝕏 := {
    base := @PartOrd.ofHom [𝕏]ᵈ.X [[𝕏]ᵈ]ᵈ.X _ _
      ⟨fun x => x, fun a b hab => by rw [hab]⟩
    hasDeriv :=
      ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => ⟨⟩, fun _ _ _ => le_rfl⟩, fun x dx hx => ⟨hx, rfl⟩⟩
  }

end disc

end Section8

section Section9

-- TODO semilattices

end Section9

end Change

end Section6

end Chapter4

section Chapter5

-- TODO graph algorithms

end Chapter5

section Chapter6

universe u

namespace Adamek

variable (F : Type u ⥤ Type u)

def step : ∀ n, F.obj^[n] PEmpty → F.obj^[n + 1] PEmpty
  | 0 => PEmpty.elim
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.map (step n)

def mapLE {m : ℕ} : (n : ℕ) → m ≤ n → (F.obj^[m] PEmpty → F.obj^[n] PEmpty)
  | 0, h => (Nat.le_zero.mp h) ▸ id
  | n + 1, h =>
    if heq : m = n + 1 then heq ▸ id
    else step F n ∘ mapLE n (by omega)

theorem mapLE_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : F.obj^[a] PEmpty) :
    mapLE F c (hab.trans hbc) x = mapLE F c hbc (mapLE F b hab x) := by
  induction c generalizing a b with
  | zero =>
    obtain rfl := Nat.le_zero.mp hbc
    obtain rfl := Nat.le_zero.mp hab
    rfl
  | succ k ih =>
    by_cases hb : b = k + 1
    · subst hb
      by_cases ha : a = k + 1
      · subst ha; simp only [mapLE, dite_true]; rfl
      · simp only [mapLE, dite_true, dif_neg ha, Function.comp_apply]; rfl
    · by_cases ha : a = k + 1
      · omega
      · simp only [mapLE, dif_neg ha, dif_neg hb, Function.comp_apply]
        exact congrArg (step F k) (ih hab (by omega) x)

def chain : ℕ ⥤ Type u where
  obj n := F.obj^[n] PEmpty
  map f := mapLE F _ f.down.down
  map_id n := by
    ext x
    simp only [types_id_apply]
    cases n with
    | zero => simp [mapLE]
    | succ n => simp [mapLE]
  map_comp {a b c} f g := by
    ext x
    simp only [types_comp_apply]
    exact mapLE_trans F f.down.down g.down.down x

def μ := colimit (chain F)

end Adamek

end Chapter6
