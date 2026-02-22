import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Order.Category.PartOrd
import Mathlib.Tactic.Recall

open CategoryTheory Limits

section Exercise1

/-! Define two different monoids whose carrier is the natural numbers. -/

instance : Monoid ℕ where
  one := 0
  mul := Nat.add
  mul_one := Nat.add_zero
  one_mul := Nat.zero_add
  mul_assoc := Nat.add_assoc

instance : Monoid ℕ where
  one := 1
  mul := Nat.mul
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_assoc := Nat.mul_assoc

end Exercise1

section Exercise2

/-! Add a property to the definition of monoid to make it into a commutative monoid. -/

#check CommMonoid

class CommMonoid' M extends Monoid M where
  mul_comm : ∀ x y : M, x * y = y * x

end Exercise2

section Exercise3

/-!
What are the initial and final objects in Poset, the category of partially ordered sets and
monotone functions?
-/

/-- Partially ordered singleton set. -/
def PartOrd.terminal : PartOrd := PartOrd.of PUnit

/-- Partially ordered empty set. -/
def PartOrd.initial : PartOrd := PartOrd.of PEmpty

def PartOrd.isTerminal : IsTerminal PartOrd.terminal :=
  IsTerminal.ofUniqueHom
    (fun _ => PartOrd.ofHom ⟨fun _ => ⟨⟩, fun _ _ _ => le_rfl⟩)
    (fun _ _ => PartOrd.ext fun _ => rfl)

def PartOrd.isInitial : IsInitial PartOrd.initial :=
  IsInitial.ofUniqueHom
    (fun _ => PartOrd.ofHom ⟨PEmpty.elim, fun x => x.elim⟩)
    (fun _ _ => PartOrd.ext fun x => x.elim)

instance : HasTerminal PartOrd :=
  IsTerminal.hasTerminal PartOrd.isTerminal

instance : HasInitial PartOrd :=
  IsInitial.hasInitial PartOrd.isInitial

end Exercise3

section Exercise4

/-!
What are the initial and final objects in CMon, the category of commutative monoids and
monoid homomorphisms?
-/

/-- The zero object (terminal and initial) is the commutative monoid on a singleton set. -/
def CommMonCat.zero : CommMonCat := CommMonCat.of PUnit

def CommMonCat.isTerminal : IsTerminal CommMonCat.zero :=
  IsTerminal.ofUniqueHom
    (fun _ => CommMonCat.ofHom {
      toFun _ := 1
      map_one' := rfl
      map_mul' _ _ := rfl
    })
    (fun _ _ => CommMonCat.ext fun _ => rfl)

def CommMonCat.isInitial : IsInitial CommMonCat.zero :=
  IsInitial.ofUniqueHom
    (fun _ => CommMonCat.ofHom {
      toFun _ := 1
      map_one' := rfl
      map_mul' _ _ := (one_mul 1).symm
    })
    (fun _ m => CommMonCat.ext fun ⟨⟩ => m.hom.map_one)

instance : HasTerminal CommMonCat :=
  IsTerminal.hasTerminal CommMonCat.isTerminal

instance : HasInitial CommMonCat :=
  IsInitial.hasInitial CommMonCat.isInitial

end Exercise4

section Exercise5

/-!
What do products in Rel, the category of sets and relations, look like? (Hint. The product of `A`
and `B` is not the cartesian product of sets!)
-/

/-! The product is the disjoint union -/

universe u

open SetRel Function

def RelCat.prodFan (X Y : RelCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk
    (.ofRel (graph Sum.inl).inv)
    (.ofRel (graph Sum.inr).inv)

private def RelCat.prodLift {W X Y : RelCat.{u}} (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ (X ⊕ Y : Type u) :=
  .ofRel {p | (∃ x, p.2 = .inl x ∧ (p.1, x) ∈ f.rel) ∨
              (∃ y, p.2 = .inr y ∧ (p.1, y) ∈ g.rel)}

private lemma RelCat.prodLift_inl {W X Y : RelCat.{u}} (f : W ⟶ X) (g : W ⟶ Y) (w x) :
    (w, Sum.inl x) ∈ (prodLift f g).rel ↔ (w, x) ∈ f.rel := by
  apply Iff.intro
  · rintro (⟨x', hx', h⟩ | ⟨y', hy', _⟩)
    · exact Sum.inl.inj hx' ▸ h
    · exact absurd hy' nofun
  · exact fun h => .inl ⟨x, rfl, h⟩

private lemma RelCat.prodLift_inr {W X Y : RelCat.{u}} (f : W ⟶ X) (g : W ⟶ Y) (w y) :
    (w, Sum.inr y) ∈ (prodLift f g).rel ↔ (w, y) ∈ g.rel := by
  apply Iff.intro
  · rintro (⟨x', hx', _⟩ | ⟨y', hy', h⟩)
    · exact absurd hx' nofun
    · exact Sum.inr.inj hy' ▸ h
  · exact fun h => .inr ⟨y, rfl, h⟩

private lemma RelCat.comp_fst_rel {W X Y : RelCat.{u}} (m : W ⟶ (X ⊕ Y)) w x :
    (w, x) ∈ (m ≫ (prodFan X Y).fst).rel ↔ (w, Sum.inl x) ∈ m.rel :=
  ⟨fun ⟨_, hm, heq⟩ => heq ▸ hm, fun hm => ⟨_, hm, rfl⟩⟩

private lemma RelCat.comp_snd_rel {W X Y : RelCat.{u}} (m : W ⟶ (X ⊕ Y)) w y :
    (w, y) ∈ (m ≫ (prodFan X Y).snd).rel ↔ (w, Sum.inr y) ∈ m.rel :=
  ⟨fun ⟨_, hm, heq⟩ => heq ▸ hm, fun hm => ⟨_, hm, rfl⟩⟩

def RelCat.prodFan_isLimit (X Y : RelCat.{u}) : IsLimit (RelCat.prodFan X Y) := by
  apply BinaryFan.isLimitMk
  case lift =>
    exact fun s => prodLift s.fst s.snd
  case fac_left =>
    intro s
    apply RelCat.Hom.ext
    ext ⟨w, x⟩
    exact (comp_fst_rel _ w x).trans (prodLift_inl _ _ w x)
  case fac_right =>
    intro s
    apply RelCat.Hom.ext
    ext ⟨w, y⟩
    exact (comp_snd_rel _ w y).trans (prodLift_inr _ _ w y)
  case uniq =>
    intro s m hfst hsnd
    ext ⟨w, z⟩
    cases z with
    | inl x =>
      rw [prodLift_inl]
      exact (comp_fst_rel m w x).symm.trans (Set.ext_iff.mp (congr_arg _ hfst) _)
    | inr y =>
      rw [prodLift_inr]
      exact (comp_snd_rel m w y).symm.trans (Set.ext_iff.mp (congr_arg _ hsnd) _)

instance (X Y : RelCat) : HasLimit (pair X Y) :=
  HasLimit.mk ⟨RelCat.prodFan X Y, RelCat.prodFan_isLimit X Y⟩

instance : HasBinaryProducts RelCat :=
  hasBinaryProducts_of_hasLimit_pair RelCat

end Exercise5

section Exercise6

universe u

/-!
The signature for `Inductive` has a comment saying that out is not strictly necessary. Show that
you can implement out using `fold`, `into` and `F.map`. Why did we include it in the API
nonetheless?
-/

open Endofunctor

structure Inductive (F : Type u ⥤ Type u) where
  /-- Carrier `alg.a` and algebra map `alg.str` -/
  alg : Algebra F
  isInitial : IsInitial alg

variable {F : Type u ⥤ Type u} (I : Inductive F) {α : Type u}

def Inductive.fold (alg : F.obj α → α) : I.alg.a → α :=
  (I.isInitial.to ⟨α, alg⟩).f

def Inductive.into : F.obj I.alg.a → I.alg.a := I.alg.str

def Inductive.out : I.alg.a → F.obj I.alg.a :=
  Algebra.Initial.strInv I.isInitial

def Inductive.out' : I.alg.a → F.obj I.alg.a :=
  I.fold (F.map I.into)

example : I.out = I.out' := rfl

/-!
The `fold`-based implementation is O(n), which is inefficient.
However, `out` can be implemented in O(1).
-/

end Exercise6

section Exercise7

/-! Prove that `〚F〛` defines a functor for all `F`. -/

universe u

/-- Grammar of polynomial functors. -/
inductive PolynomialFunctor where
  | id
  | const (A : Type u)
  | prod (F G : PolynomialFunctor)
  | coprod (F G : PolynomialFunctor)

set_option hygiene false in
/-- Turn off hygiene to allow notation to be used within its definition -/
notation "〚" F "〛" => PolynomialFunctor.denotation F

/--
Interpretation of the grammar.

We inductively show that the interpretation defines a valid functor.
-/
def PolynomialFunctor.denotation : PolynomialFunctor → Type u ⥤ Type u
  | id => 𝟭 (Type u)
  | const A => Functor.const (Type u) |>.obj A
  | prod F G => {
      obj X := 〚F〛.obj X × 〚G〛.obj X
      map f := Prod.map (〚F〛.map f) (〚G〛.map f)
      map_id := by
        intro
        simp only [Functor.map_id]
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
        simp only [Functor.map_id]
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

variable (F : PolynomialFunctor.{u})
#check 〚F〛

end Exercise7

section Exercise8

/-!
Recall that if an object `A` and a family of maps `f i : A → X i` form a cone over a projective
diagram, the mediating map `f↠` can be explicitly given as `f↠(a) = i ↦ f i a`.
Verify that if there is any other `h : A → lim X_i` such that `f_i = h ≫ π_i` for every `i`,
then `h = f↠`.
-/

universe u

variable {ι : Type u} {X : ι → Type u} {A : Type u} (f : Π i, A → X i)

/-- Projection -/
def π (i : ι) : (Π i, X i) → X i := fun x => x i

/-- The mediating map -/
def mediate (a : A) : Π i, X i := fun i => f i a

postfix:max "↠" => mediate

/-- Uniqueness -/
theorem mediate_unique (h : A → Π i, X i) (hh : ∀ i, π i ∘ h = f i) : h = f↠ := by
  funext (a : A) (i : ι)
  -- We want to show:
  show h a i = f↠ a i
  -- We have
  have hh : π i ∘ h = f i := hh i
  -- So
  calc h a i
    _ = π i (h a) := rfl -- By definition
    _ = f i a := congrFun hh a
    _ = f↠ a i := rfl -- By definition

end Exercise8

section Exercise9

/-!
The Levenshtein distance, or edit distance, between two strings be naively computed as follows:
-/

variable {α : Type} [DecidableEq α]

/-- Levenshtein distance -/
def lev : List α × List α → ℕ
  | (s₁, []) => s₁.length
  | ([], s₂) => s₂.length
  | (s₁@(c₁ :: s₁'), s₂@(c₂ :: s₂')) =>
    if c₁ = c₂ then
      lev (s₁', s₂')
    else
      min
        (min (lev (s₁, s₂')) (lev (s₁', s₂)))
        (lev (s₁', s₂'))
        + 1
termination_by s => s.1.length + s.2.length

#guard lev ([1, 5, 2, 3], [1, 2, 4, 3]) == 2
#guard lev ([1, 2, 3], [1, 2, 3]) == 0

/-!
Formulate this algorithm as a coalgebra-to-algebra morphism, and then solve with dynamic
programming.
-/

inductive Split (α R : Type)
  | inl : List α → Split α R
  | inr : List α → Split α R
  | cons : R → Split α R
  | diff : R → R → R → Split α R

def Split.map {R S} (f : R → S) : Split α R → Split α S
  | Split.inl n₁ => Split.inl n₁
  | Split.inr n₂ => Split.inr n₂
  | Split.cons x => Split.cons (f x)
  | Split.diff x y z => Split.diff (f x) (f y) (f z)

/-- Split is indeed a lawful functor -/
def Split.functor : Type ⥤ Type where
  obj := Split α
  map := Split.map
  map_id := by intro; ext x; cases x <;> rfl
  map_comp := by intros; ext x; cases x <;> rfl

def Split.coalg : List α × List α → Split α (List α × List α)
  | (s₁, []) => Split.inl s₁
  | ([], s₂) => Split.inr s₂
  | (s₁@(c₁ :: s₁'), s₂@(c₂ :: s₂')) =>
    if c₁ = c₂ then
      Split.cons (s₁', s₂')
    else
      Split.diff (s₁, s₂') (s₁', s₂) (s₁', s₂')

def Split.alg : Split α ℕ → ℕ
  | Split.inl s₁ => s₁.length
  | Split.inr s₂ => s₂.length
  | Split.cons x => x
  | Split.diff x y z => min (min x y) z + 1

/-- Partial because well-foundedness is not checked -/
partial def Split.hylo {β σ} [Inhabited β] (coalg : α → Split σ α) (alg : Split σ β → β) : α → β :=
  alg ∘ map (hylo coalg alg) ∘ coalg

def lev₂ : List α × List α → ℕ := Split.hylo Split.coalg Split.alg

#guard lev₂ ([1, 5, 2, 3], [1, 2, 4, 3]) == 2
#guard lev₂ ([1, 2, 3], [1, 2, 3]) == 0

/-- Version of `map` handling mutable state. -/
def Split.mapM {m F G} [Applicative m] (f : F → m G) : Split α F → m (Split α G)
  | .inl s => pure (.inl s)
  | .inr s => pure (.inr s)
  | .cons x => .cons <$> f x
  | .diff x y z => .diff <$> f x <*> f y <*> f z

-- We require α to be hashable for memoisation
variable [Hashable α]

/-- Memoised version for dynamic programming -/
unsafe def Split.memo {β σ}
    (coalg : α → Split σ α)
    (alg : Split σ β → β) :
    α → β :=
  let rec lev (x : α) : StateM (Std.HashMap α β) β := do
    match (← get)[x]? with
    | some v => return v
    | none => do
      let v := alg (← Split.mapM lev (coalg x))
      modify (·.insert x v)
      return v
  fun x => (lev x).run' ∅

unsafe def lev₃ : List α × List α → ℕ :=
  Split.memo Split.coalg Split.alg

#eval lev₃ ([1, 5, 2, 3], [1, 2, 4, 3]) == 2
#eval lev₃ ([1, 2, 3], [1, 2, 3]) == 0
#eval lev₃ (List.range 100, 1 :: List.range 100) == 1

end Exercise9
