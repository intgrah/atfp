import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Order.Category.PartOrd

open CategoryTheory Limits

section Exercise1

/-! Define two different monoids whose carrier is the natural numbers. -/

example : Monoid ℕ where
  one := 0
  mul := Nat.add
  mul_one := Nat.add_zero
  one_mul := Nat.zero_add
  mul_assoc := Nat.add_assoc

example : Monoid ℕ where
  one := 1
  mul := Nat.mul
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_assoc := Nat.mul_assoc

end Exercise1

section Exercise2

/-! Add a property to the definition of monoid to make it into a commutative monoid. -/

class CommMonoid' M extends Monoid M where
  mul_comm : ∀ x y : M, x * y = y * x

end Exercise2

section Exercise3

/-!
What are the initial and final objects in Poset, the category of partially ordered sets and
monotone functions?
-/

/-- Partially ordered singleton set with trivial reflexive order -/
def PartOrd.terminal : PartOrd := PartOrd.of PUnit

/-- Send every element to the unit -/
def PartOrd.isTerminal : IsTerminal PartOrd.terminal :=
  IsTerminal.ofUniqueHom
    (fun X => PartOrd.ofHom ⟨fun (_ : X) => ⟨⟩, fun (a b : X) (_ : a ≤ b) => le_rfl⟩)
    (fun X (f : X ⟶ terminal) => PartOrd.ext fun x => (rfl : f x = f x))

/-- Partially ordered empty set with empty order -/
def PartOrd.initial : PartOrd := PartOrd.of PEmpty

/-- Eliminate the element -/
def PartOrd.isInitial : IsInitial PartOrd.initial :=
  IsInitial.ofUniqueHom
    (fun _ => PartOrd.ofHom ⟨nofun, nofun⟩)
    (fun _ _ => PartOrd.ext nofun)

instance : HasTerminal PartOrd := PartOrd.isTerminal.hasTerminal
instance : HasInitial PartOrd := PartOrd.isInitial.hasInitial

end Exercise3

section Exercise4

/-!
What are the initial and final objects in CMon, the category of commutative monoids and
monoid homomorphisms?
-/

/-- The zero object (terminal and initial) is the commutative monoid on a singleton set. -/
def CommMonCat.zero : CommMonCat := CommMonCat.of PUnit

/-- Send every element to the unit -/
def CommMonCat.isTerminal : IsTerminal CommMonCat.zero :=
  IsTerminal.ofUniqueHom
    (fun _ => ofHom ⟨⟨fun _ => 1, rfl⟩, fun _ _ => rfl⟩)
    (fun _ _ => ext fun _ => rfl)

/-- Send every element to the identity -/
def CommMonCat.isInitial : IsInitial CommMonCat.zero :=
  IsInitial.ofUniqueHom
    (fun _ => ofHom ⟨⟨fun ⟨⟩ => 1, rfl⟩, fun ⟨⟩ ⟨⟩ => (one_mul 1).symm⟩)
    (fun _ m => ext fun ⟨⟩ => m.hom.map_one)

instance : HasTerminal CommMonCat := CommMonCat.isTerminal.hasTerminal
instance : HasInitial CommMonCat := CommMonCat.isInitial.hasInitial

end Exercise4

section Exercise5

/-!
What do products in Rel, the category of sets and relations, look like? (Hint. The product of `A`
and `B` is not the cartesian product of sets!)
-/

/-! The product is the disjoint union (as well as the coproduct) -/

universe u

variable {W X Y : RelCat.{u}}

open SetRel Function

/--
xy : X ⊕ Y is related to x : X iff xy = .inl x,
xy : X ⊕ Y is related to y : Y iff xy = .inr y
-/
def RelCat.prodFan (X Y : RelCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk
    ⟨{(xy, x) | xy = Sum.inl x}⟩
    ⟨{(xy, y) | xy = Sum.inr y}⟩

def RelCat.prodLift (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊕ Y :=
  ⟨{(w, xy) | match xy with | .inl x => (w, x) ∈ f.rel | .inr y => (w, y) ∈ g.rel}⟩

lemma RelCat.comp_fst_rel (m : W ⟶ X ⊕ Y) w x :
    (w, x) ∈ (m ≫ (prodFan X Y).fst).rel ↔ (w, Sum.inl x) ∈ m.rel :=
  ⟨fun ⟨.inl _, hm, heq⟩ => heq ▸ hm, fun hm => ⟨.inl x, hm, rfl⟩⟩

lemma RelCat.comp_snd_rel (m : W ⟶ X ⊕ Y) w y :
    (w, y) ∈ (m ≫ (prodFan X Y).snd).rel ↔ (w, Sum.inr y) ∈ m.rel :=
  ⟨fun ⟨.inr _, hm, heq⟩ => heq ▸ hm, fun hm => ⟨.inr y, hm, rfl⟩⟩

def RelCat.prodFan_isLimit : IsLimit (prodFan X Y) := by
  apply BinaryFan.isLimitMk fun s => prodLift s.fst s.snd
  case fac_left => intro; ext; apply comp_fst_rel
  case fac_right => intro; ext; apply comp_snd_rel
  case uniq =>
    intro _ _ hfst hsnd
    ext ⟨w, x | y⟩
    · rw [← comp_fst_rel, ← hfst]; rfl
    · rw [← comp_snd_rel, ← hsnd]; rfl

instance (X Y : RelCat) : HasLimit (pair X Y) :=
  ⟨RelCat.prodFan X Y, RelCat.prodFan_isLimit⟩

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
However, `out` can be implemented in O(1) when the isomorphism
is simply a wrapper type (as in OCaml).
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
      map_id X := by
        rw [〚F〛.map_id, 〚G〛.map_id]
        rfl
      map_comp f g := by
        rw [〚F〛.map_comp, 〚G〛.map_comp]
        rfl
    }
  | coprod F G => {
      obj X := 〚F〛.obj X ⊕ 〚G〛.obj X
      map f := Sum.map (〚F〛.map f) (〚G〛.map f)
      map_id X := by
        rw [〚F〛.map_id, 〚G〛.map_id]
        exact Sum.map_id_id
      map_comp f g := by
        rw [〚F〛.map_comp, 〚G〛.map_comp]
        ext (_ | _) <;> rfl
    }

end Exercise7

section Exercise8

/-!
Recall that if an object `A` and a family of maps `f i : A → X i` form a cone over a projective
diagram, the mediating map `f↠` can be explicitly given as `f↠(a) = i ↦ f i a`.
Verify that if there is any other `h : A → limit X` such that `f i = h ≫ π i` for every `i`,
then `h = f↠`.
-/

universe u

variable {ι : Type u} {X : ι → Type u} {A : Type u} (f : Π i, A → X i)

def π (i : ι) : (Π i, X i) → X i := fun x => x i
def mediate (a : A) : Π i, X i := fun i => f i a

postfix:max "↠" => mediate

/-- Uniqueness -/
theorem mediate_unique (h : A → Π i, X i) (hh : ∀ i, π i ∘ h = f i) : h = f↠ := by
  show h = f↠
  -- Let a : A and i : ι
  funext (a : A) (i : ι)
  -- We want to show
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

variable {α : Type} [DecidableEq α] [Hashable α]

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

/-- info: 2 -/
#guard_msgs in
#eval lev ([1, 5, 2, 3], [1, 2, 4, 3])
/-- info: 0 -/
#guard_msgs in
#eval lev ([1, 2, 3], [1, 2, 3])

/-!
Formulate this algorithm as a coalgebra-to-algebra morphism, and then solve with dynamic
programming.
-/

inductive Split.obj (α R : Type)
  | inl (s₁ : List α)
  | inr (s₂ : List α)
  | cons (x : R)
  | diff (x y z : R)

def Split.map {R S} (f : R → S) : obj α R → obj α S
  | .inl s₁ => .inl s₁
  | .inr s₂ => .inr s₂
  | .cons x => .cons (f x)
  | .diff x y z => .diff (f x) (f y) (f z)

/-- Split is indeed a lawful functor -/
def Split (α : Type) : Type ⥤ Type where
  obj := Split.obj α
  map := Split.map
  map_id _ := by ext (_ | _ | _ | _) <;> rfl
  map_comp _ _ := by ext (_ | _ | _ | _) <;> rfl

open Endofunctor (Algebra Coalgebra)

abbrev Split.coalg : Coalgebra (Split α) where
  V := List α × List α -- carrier
  str -- structure morphism from V ⟶ Split.obj α V
    | (s₁, []) => .inl s₁
    | ([], s₂) => .inr s₂
    | (s₁@(c₁ :: s₁'), s₂@(c₂ :: s₂')) =>
      if c₁ = c₂ then
        .cons (s₁', s₂')
      else
        .diff (s₁, s₂') (s₁', s₂) (s₁', s₂')

abbrev Split.alg : Algebra (Split α) where
  a := ℕ -- carrier
  str -- structure morphism from Split.obj α a ⟶ a
    | .inl s₁ => s₁.length
    | .inr s₂ => s₂.length
    | .cons x => x
    | .diff x y z => min (min x y) z + 1

/-- Partial because well-foundedness is not proven -/
partial def Split.hylo {α}
    (coalg : Coalgebra (Split α))
    (alg : Algebra (Split α)) [Inhabited alg.a] :
    coalg.V → alg.a :=
  alg.str ∘ map (hylo coalg alg) ∘ coalg.str

def lev₂ : List α × List α → ℕ := Split.hylo Split.coalg Split.alg

/-- info: 2 -/
#guard_msgs in
#eval lev₂ ([1, 5, 2, 3], [1, 2, 4, 3])
/-- info: 0 -/
#guard_msgs in
#eval lev₂ ([1, 2, 3], [1, 2, 3])

/-- Version of `map` handling mutable state. -/
def Split.mapM {m F G} [Applicative m] (f : F → m G) : obj α F → m (obj α G)
  | .inl s => pure (.inl s)
  | .inr s => pure (.inr s)
  | .cons x => .cons <$> f x
  | .diff x y z => .diff <$> f x <*> f y <*> f z

/-- Memoised version for dynamic programming -/
unsafe def Split.memo
    (coalg : Coalgebra (Split α)) [BEq coalg.V] [Hashable coalg.V]
    (alg : Algebra (Split α)) :
    coalg.V → alg.a :=
  let rec lev (x : coalg.V) : StateM (Std.HashMap coalg.V alg.a) alg.a := do
    match (← get)[x]? with
    | some v => return v
    | none => do
      let v := alg.str (← mapM lev (coalg.str x))
      modify (·.insert x v)
      return v
  fun x => (lev x).run' ∅

unsafe def lev₃ : List α × List α → ℕ :=
  Split.memo Split.coalg Split.alg

/-- info: 2 -/
#guard_msgs in
#eval lev₃ ([1, 5, 2, 3], [1, 2, 4, 3])
/-- info: 0 -/
#guard_msgs in
#eval lev₃ ([1, 2, 3], [1, 2, 3])

/- [0, ... 99] and [1, 0, ... 99] would be intractable if not for memoisation -/
/-- info: 1 -/
#guard_msgs in
#eval lev₃ (List.range 100, 1 :: List.range 100)

end Exercise9
