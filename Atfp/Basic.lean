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
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Order.Category.PartOrd

open CategoryTheory Limits

section Chapter1

end Chapter1

section Chapter2

section Section1

/-! Example 2.1.1 -/

variable [inst : Monoid M]
#check Monoid
#check inst.one
#check inst.mul
#check inst.one_mul
#check inst.mul_one
#check inst.mul_assoc

/-! Example 2.1.2 -/

#check Nat.instAddMonoid

instance : Monoid (X → X) where
  one := @id X
  mul f g := f ∘ g
  one_mul := Function.id_comp
  mul_one := Function.comp_id
  mul_assoc := Function.comp_assoc
variable [Semiring X] (n : Nat)

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
#check inst.toLE.le
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

variable [Monoid M] [Monoid N] (f : MonoidHom M N)
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

variable [Group M'] [Group N'] (f : MonoidHom M' N')
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

/-! Definition 2.3.1 -/

variable [inst : Category 𝓒] (X Y Z : 𝓒) (f : X ⟶ Y) (g : Y ⟶ Z)
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

def Matrix.instCategory [Semiring S] : Category ℕ where
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

#check exp

-- TODO

end Section3

end Section3

end Chapter2

section Chapter3

section Section1

#check Nat
#check Nat.zero
#check Nat.succ
abbrev Nat.one := succ zero
abbrev Nat.two := succ one
abbrev Nat.three := succ two

def Nat.double : Nat → Nat
  | zero => zero
  | succ n => succ (succ (double n))

#check Nat.add
#check Nat.mul
#check Nat.repeat

def Nat.fold' (z : α) (s : α → α) : Nat → α
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
  obj X := Sum PUnit X
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
  hom_inv_id := by ext x; cases x <;> rfl
  inv_hom_id := by ext x; cases x <;> rfl

def Nat.foldO (zs : Sum PUnit α → α) : μN → α :=
  Nat.fold' (zs (.inl ())) (zs ∘ .inr)

example : Nat.foldO f Nat.zero = f (.inl ()) := rfl
example : Nat.foldO f (Nat.succ k) = f (.inr (Nat.foldO f k)) := rfl

example : Nat.foldO f (in' (.inl ())) = f (.inl ()) := rfl
example : Nat.foldO f (in' (.inr k)) = f (.inr (Nat.foldO f k)) := rfl

def Nat.foldO_str : Nat.foldO f ∘ in' = f ∘ N.map (Nat.foldO f) := by
  ext x
  cases x <;> rfl

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

universe u

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
        ext a
        cases a with
        | inl => simp only [Sum.map_inl, types_id_apply]
        | inr => simp only [Sum.map_inr, types_id_apply]
      map_comp := by
        intros
        ext
        simp only [Functor.map_comp, types_comp_apply, Sum.map_map]
        rfl
    }

def μ (F : PolynomialFunctor.{u}) :=
  Limits.colimit 〚F〛

/-! Lemma 3.4.2 -/

def PolynomialFunctor.monotone (F : PolynomialFunctor) (f : α ↪ β) :
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

def Inductive.fold (alg : F.obj α → α) : I.alg.a → α :=
  (I.isInitial.to ⟨α, alg⟩).f

def Inductive.into : F.obj I.alg.a → I.alg.a := I.alg.str

def Inductive.out : I.alg.a → F.obj I.alg.a :=
  Algebra.Initial.strInv I.isInitial

end Section5

section Section9

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
    ext ⟨x1, y1⟩ ⟨x2, y2⟩
    dsimp only [ℛ]
    rw [ihF, ihG, Prod.mk.injEq]
  | coprod F G ihF ihG =>
    ext x y
    dsimp only [ℛ]
    cases x <;> cases y
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

universe u

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

def D (pre : Preord) : Preord where
  carrier := pre.carrier
  str := {
    le := Eq
    lt a b := a = b ∧ b ≠ a
    le_refl := Eq.refl
    le_trans _ _ _ := Eq.trans
  }

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

/-! Definition 4.1.1 -/

variable [inst₁ : SemilatticeSup X] [inst₂ : OrderBot X]
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

end Chapter4

section Chapter6

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
