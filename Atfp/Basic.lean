import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib

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

#check Set.instCompleteAtomicBooleanAlgebra.toCompleteLattice.toPartialOrder

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

open CategoryTheory

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

open Limits

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

open CategoryTheory Endofunctor

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

def μN := ℕ

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
#check Algebra.instCategory N
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

inductive PolynomialFunctor where
  | id
  | const (A : Type u)
  | prod (F G : PolynomialFunctor)
  | coprod (F G : PolynomialFunctor)

def PolynomialFunctor.denotation : PolynomialFunctor → Type u ⥤ Type u
  | id => 𝟭 (Type u)
  | const A => Functor.const (Type u) |>.obj A
  | prod F G => {
      obj X := F.denotation.obj X × G.denotation.obj X
      map f := Prod.map (F.denotation.map f) (G.denotation.map f)
    }
  | coprod F G => {
      obj X := F.denotation.obj X ⊕ G.denotation.obj X
      map f := Sum.map (F.denotation.map f) (G.denotation.map f)
    }

notation "〚" P "〛" => PolynomialFunctor.denotation P

/-! Lemma 3.4.2 -/

def PolynomialFunctor.monotone (P : PolynomialFunctor) {α β : Type u} (f : α ↪ β) :
    〚P〛.obj α ↪ 〚P〛.obj β where
  toFun := 〚P〛.map f
  inj' := by
    induction P with
    | id => exact f.inj'
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

def PolynomialFunctor.iterate_embedding (P : PolynomialFunctor) (n : ℕ) :
    〚P〛.obj^[n] PEmpty ↪ 〚P〛.obj^[n + 1] PEmpty := by
  induction n with
  | zero => exact ⟨PEmpty.elim, fun x => PEmpty.elim x⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact P.monotone ih

-- TODO

end Section4

section Section5

#check Functor

variable (F : Type u ⥤ Type u)

structure Inductive where
  T : Type u
  into : F.obj T → T
  out : T → F.obj T
  fold : (F.obj α → α) → T → α

end Section5

end Chapter3

universe u

variable (α : Type u) [Preorder α]

def WF (α : Type u) [Preorder α] : Prop :=
  ¬∃ chain : ℕ → α, ∀ n, chain n > chain (n + 1)

def D (pre : Preord) : Preord where
  carrier := pre.carrier
  str := {
    le := Eq
    lt a b := a = b ∧ b ≠ a
    le_refl := Eq.refl
    le_trans _ _ _ := Eq.trans
  }

def WF2 (α : Type u) [Preorder α] : Prop :=
  ∀ A : Set α, Inhabited A → ∃ a : A, ∀ b : A, b ≤ a → a ≤ b

theorem iff {α : Type u} [Preorder α] : WF α ↔ WF2 α := by
  apply Iff.intro
  · intro wf A ⟨x⟩
    -- Making classical lemmas explicit
    apply Classical.byContradiction
    intro h
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
