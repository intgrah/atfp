module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.Data.Rel

@[expose] public section

open CategoryTheory Limits

universe u

section Section1

variable {α : Type u}

#check Nat
#check Nat.zero
#check Nat.succ

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
  map_id := by intro; funext x; cases x <;> rfl
  map_comp := by intros; funext x; cases x <;> rfl

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

def initial.isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom
    (fun ⟨A, f⟩ => ⟨Nat.foldO f, Nat.foldO_str.symm⟩) <| by
    -- Suppose that we have another map h
    intro ⟨A, f⟩ ⟨h, hh⟩
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
        _ = h ∘ in' ∘ out := congrArg (· ∘ out) hh
        _ = h ∘ id := congrArg (h ∘ ·) this
        _ = h := Function.comp_id h
    -- Similarly
    have h₂ :=
      calc f ∘ N.map (Nat.foldO f) ∘ out
        _ = Nat.foldO f ∘ in' ∘ out := congrArg (· ∘ out) Nat.foldO_str.symm
        _ = Nat.foldO f ∘ id := congrArg (Nat.foldO f ∘ ·) this
        _ = Nat.foldO f := Function.comp_id (Nat.foldO f)
    -- Now we show that for all x : μN, we have that h x = Nat.foldO f x
    ext (x : μN)
    show h x = Nat.foldO f x
    -- We first note that x : μN means that there exists an n : ℕ such that x : N.obj^[n] 0
    -- have : ∃ n : ℕ, x = n := ⟨x, rfl⟩
    induction x with
    | zero =>
      calc h .zero
        _ = (f ∘ N.map h ∘ out) .zero := by rw [h₁]
        _ = (f ∘ N.map h) (out .zero) := rfl
        _ = (f ∘ N.map h) (.inl ()) := rfl
        _ = f (N.map h (.inl ())) := rfl
        _ = f (.inl ()) := rfl
        _ = f (N.map (Nat.foldO f) (.inl ())) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (.inl ()) := rfl
        _ = (f ∘ N.map (Nat.foldO f)) (out .zero) := rfl
        _ = (f ∘ N.map (Nat.foldO f) ∘ out) .zero := rfl
        _ = Nat.foldO f .zero := rfl
    | succ k ih =>
      calc h (.succ k)
        _ = (f ∘ N.map h ∘ out) (.succ k) := by rw [h₁]
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

namespace PolynomialFunctor

set_option hygiene false in
notation "〚" F "〛" => PolynomialFunctor.denotation F

def denotation : PolynomialFunctor → Type u ⥤ Type u
  | id => 𝟭 (Type u)
  | const A => Functor.const (Type u) |>.obj A
  | prod F G => FunctorToTypes.prod 〚F〛 〚G〛
  | coprod F G => FunctorToTypes.coprod 〚F〛 〚G〛

def μ (F : PolynomialFunctor.{u}) :=
  Limits.colimit 〚F〛

/-! Lemma 3.4.2 -/

def monotone {α β} (F : PolynomialFunctor) (f : α ↪ β) :
    〚F〛.obj α ↪ 〚F〛.obj β where
  toFun := 〚F〛.map f
  inj' := by
    induction F with
    | id => exact f.injective
    | const A => intro x y h; exact h
    | prod F G ihF ihG =>
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      simp only [denotation, FunctorToTypes.prod, Prod.mk.injEq] at h ⊢
      exact ⟨ihF h.1, ihG h.2⟩
    | coprod F G ihF ihG =>
      rintro (a₁ | a₂) (b₁ | b₂) h
      all_goals
        simp only [denotation, FunctorToTypes.coprod, reduceCtorEq,
          Sum.inl.injEq, Sum.inr.injEq] at h
      · exact congrArg Sum.inl (ihF h)
      · exact congrArg Sum.inr (ihG h)

/-! Lemma 3.4.3 -/

def iterate_embedding (F : PolynomialFunctor) (n : ℕ) :
    〚F〛.obj^[n] PEmpty ↪ 〚F〛.obj^[n + 1] PEmpty := by
  induction n with
  | zero => exact ⟨nofun, nofun⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.monotone ih

end PolynomialFunctor

end Section4

section Section5

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

def PolynomialFunctor.ℛ (R : Rel A B) (F : PolynomialFunctor) : Rel (〚F〛.obj A) (〚F〛.obj B) :=
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
    simp only [ihF, ihG]
    constructor <;> intro h
    · exact Prod.ext h.1 h.2
    · exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  | coprod F G ihF ihG =>
    dsimp only [ℛ]
    ext (_ | _) (_ | _)
    · simp only [ihF]; constructor <;> intro h
      · exact congrArg Sum.inl h
      · exact Sum.inl.inj h
    · simp
    · simp
    · simp only [ihG]; constructor <;> intro h
      · exact congrArg Sum.inr h
      · exact Sum.inr.inj h

/-! Lemma 3.9.9 -/

lemma PolynomialFunctor.preserves_function {A B X Y : Type u}
    {R : Rel A X} {S : Rel B Y} {f : A → B} {g : X → Y}
    (h : (Rel.function R S) f g) :
    (Rel.function (F.ℛ R) (F.ℛ S)) (〚F〛.map f) (〚F〛.map g) := by
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

theorem WF.induction
    (hwf : WF_asc X)
    (P : X → Prop)
    (hP : ∀ x : X, (∀ y > x, P y) → P x) :
    ∀ x : X, P x := by
  intro x
  by_contra hx
  have build : ∀ x : {x : X // ¬P x}, ∃ y : {y : X // ¬P y}, x < y := by
    intro ⟨x, hnP⟩
    by_contra hall
    refine hnP (hP x fun y hy => ?_)
    by_contra hnPy
    exact hall ⟨⟨y, hnPy⟩, hy⟩
  choose next hnext using build
  let chain : ℕ → {x : X // ¬P x} := Nat.rec ⟨x, hx⟩ (fun _ => next)
  have hasc : ∀ n, (chain n).val < (chain (n + 1)).val := fun n => hnext (chain n)
  exact hwf ⟨fun n => (chain n).val, hasc⟩

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
