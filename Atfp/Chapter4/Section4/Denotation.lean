module

public import Mathlib.Order.Category.CompleteLat
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum

import Atfp.Chapter4.Section1
public import Atfp.Chapter4.Section3
public import Atfp.Chapter4.Section4.Datafun

@[expose] public section

namespace Datafun

open CategoryTheory MonoidalCategory

universe u

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
  | 1 => 𝟙_ PartOrd
  | prod A B => 〚A〛 ⊗ 〚B〛
  | arr A B => 〚A〛.exp 〚B〛
  | coprod A B => 〚A〛.coprod 〚B〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛)
  | discrete A => [〚A〛]ᵈ

lemma FinTy.toTy_denotation {T : FinTy} : 〚T〛 = 〚T.toTy〛 := by
  induction T with
  | unit => rfl
  | prod T₁ T₂ ihT₁ ihT₂ =>
    change 〚T₁〛 ⊗ 〚T₂〛 = _
    rw [ihT₁, ihT₂]
    rfl
  | coprod T₁ T₂ ihT₁ ihT₂ =>
    change 〚T₁〛.coprod 〚T₂〛 = _
    rw [ihT₁, ihT₂]
    rfl
  | powerset T => rfl
  | discrete T ihT =>
    change [〚T〛]ᵈ = _
    rw [ihT]
    rfl

instance : HasForget₂ CompleteLat PartOrd where
  forget₂.obj L := PartOrd.of L
  forget₂.map f := PartOrd.ofHom ⟨f, f.toBoundedLatticeHom.toBoundedOrderHom.toOrderHom.monotone⟩

def LatTy.bot' : ∀ L : LatTy, 〚L〛
  | .unit => ()
  | .prod L₁ L₂ => (bot' L₁, bot' L₂)
  | .powerset T => (∅ : Set 〚T〛)

def LatTy.sup' : ∀ L : LatTy, 〚L〛 → 〚L〛 → 〚L〛
  | .unit, _, _ => ()
  | .prod L₁ L₂, (x₁, x₂), (y₁, y₂) => (sup' L₁ x₁ y₁, sup' L₂ x₂ y₂)
  | .powerset T, s₁, s₂ => show Set 〚T〛 from s₁ ∪ s₂

lemma LatTy.bot'_le (L : LatTy) (x : 〚L〛) : L.bot' ≤ x := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1, ih₂ x.2⟩
  | powerset T => exact Set.empty_subset (s := x)

lemma LatTy.le_sup'_left (L : LatTy) (x y : 〚L〛) : x ≤ L.sup' x y := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1 y.1, ih₂ x.2 y.2⟩
  | powerset T => exact Set.subset_union_left (s := x) (t := y)

lemma LatTy.le_sup'_right (L : LatTy) (x y : 〚L〛) : y ≤ L.sup' x y := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1 y.1, ih₂ x.2 y.2⟩
  | powerset T => exact Set.subset_union_right (s := x) (t := y)

lemma LatTy.sup'_le (L : LatTy) {x y z : 〚L〛} (hx : x ≤ z) (hy : y ≤ z) : L.sup' x y ≤ z := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ hx.1 hy.1, ih₂ hx.2 hy.2⟩
  | powerset T => exact Set.union_subset hx hy

instance LatTy.instSemilatticeSup (L : LatTy) : SemilatticeSup 〚L〛 where
  sup := L.sup'
  le_sup_left := L.le_sup'_left
  le_sup_right := L.le_sup'_right
  sup_le _ _ _ := L.sup'_le

instance LatTy.instOrderBot (L : LatTy) : OrderBot 〚L〛 where
  bot := L.bot'
  bot_le := L.bot'_le

def LatTy.bot (L : LatTy) : PartOrd.terminal ⟶ 〚L〛 :=
  ofHom ⟨fun ⟨⟩ => L.bot', fun ⟨⟩ ⟨⟩ ⟨⟩ => le_rfl⟩

def LatTy.sup : ∀ L : LatTy, 〚L〛 ⊗ 〚L〛 ⟶ 〚L〛
  | .unit => terminal.from _
  | .prod L₁ L₂ => tensor_exchange.hom ≫ (sup L₁ ⊗ₘ sup L₂)
  | .powerset T => U.sup (PartOrd.powerset.obj 〚T〛)

def LatTy.comprehension {A : PartOrd} {X : FinTy} :
    ∀ L : LatTy, (A ⊗ [〚X〛]ᵈ ⟶ 〚L〛) → (A ⊗ 〚𝒫 X〛 ⟶ 〚L〛)
  | .unit, _ => PartOrd.terminal.from _
  | .prod L₁ L₂, f =>
    let f₁ : A ⊗ [〚X〛]ᵈ ⟶ 〚L₁〛 := f ≫ fst
    let f₂ : A ⊗ [〚X〛]ᵈ ⟶ 〚L₂〛 := f ≫ snd
    prod_lift (L₁.comprehension f₁) (L₂.comprehension f₂)
  | .powerset T, f =>
    PartOrd.ofHom {
      toFun := fun (a, (s : Set 〚X〛)) => ⋃ x ∈ s, f (a, x)
      monotone' := by
        intro (a₁, (s₁ : Set 〚X〛)) (a₂, (s₂ : Set 〚X〛)) ⟨ha, hs⟩
        apply Set.iUnion₂_subset
        intro x hx₁
        have hx₂ : x ∈ s₂ := hs hx₁
        have h₁ : f (a₁, x) ≤ f (a₂, x) := f.hom.monotone ⟨ha, le_rfl⟩
        have h₂ : f (a₂, x) ≤ ⋃ y ∈ s₂, f (a₂, y) :=
          Set.subset_biUnion_of_mem (u := fun y => f (a₂, y)) hx₂
        exact h₁.trans h₂
    }

instance FinTy.instFinite : ∀ T : FinTy, Finite 〚T〛
  | unit => Finite.of_fintype PUnit
  | prod T₁ T₂ => @Finite.instProd 〚T₁〛 〚T₂〛 T₁.instFinite T₂.instFinite
  | coprod T₁ T₂ => @Finite.instSum 〚T₁〛 〚T₂〛 T₁.instFinite T₂.instFinite
  | powerset T => @Set.instFinite 〚T〛 T.instFinite
  | discrete T => T.instFinite

instance LatTy.instFinite : ∀ L : LatTy, Finite 〚L〛
  | unit => Finite.of_fintype PUnit
  | prod L₁ L₂ => @Finite.instProd 〚L₁〛 〚L₂〛 L₁.instFinite L₂.instFinite
  | powerset T => @Set.instFinite 〚T〛 T.instFinite

def LatTy.fix {A : PartOrd} {L : LatTy}
    (f : [A]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) :
    [A]ᵈ ⟶ 〚L〛 :=
  @PartOrd.ofHom [A]ᵈ 〚L〛 _ _ {
    toFun a :=
      let f_a : 〚L〛 →o 〚L〛 :=
        ⟨fun x => f (a, x), fun _ _ hxy => f.hom.monotone ⟨rfl, hxy⟩⟩
      f_a^[L.card] ⊥
    monotone' _ _ | rfl => le_rfl
  }

theorem FinTy.nat_card_eq : ∀ T : FinTy, Nat.card 〚T〛 = T.card
  | unit => by
    change Nat.card PUnit = 1
    simp [Nat.card_eq_fintype_card]
  | prod T₁ T₂ => by
    change Nat.card (〚T₁〛 × 〚T₂〛) = T₁.card * T₂.card
    rw [Nat.card_prod, T₁.nat_card_eq, T₂.nat_card_eq]
  | coprod T₁ T₂ => by
    change Nat.card (〚T₁〛 ⊕ 〚T₂〛) = T₁.card + T₂.card
    rw [@Nat.card_sum _ _ T₁.instFinite T₂.instFinite, T₁.nat_card_eq, T₂.nat_card_eq]
  | powerset T => by
    change Nat.card (Set 〚T〛) = 2 ^ T.card
    rw [show Set 〚T〛 = (〚T〛 → Prop) from rfl, @Nat.card_fun _ _ T.instFinite, T.nat_card_eq]
    simp [Nat.card_eq_fintype_card]
  | discrete T => T.nat_card_eq

theorem LatTy.nat_card_eq : ∀ L : LatTy, Nat.card 〚L〛 = L.card
  | unit => by
    change Nat.card PUnit = 1
    simp [Nat.card_eq_fintype_card]
  | prod L₁ L₂ => by
    change Nat.card (〚L₁〛 × 〚L₂〛) = L₁.card * L₂.card
    rw [Nat.card_prod, L₁.nat_card_eq, L₂.nat_card_eq]
  | powerset T => by
    change Nat.card (Set 〚T〛) = 2 ^ T.card
    rw [show Set 〚T〛 = (〚T〛 → Prop) from rfl, @Nat.card_fun _ _ T.instFinite, T.nat_card_eq]
    simp [Nat.card_eq_fintype_card]

theorem LatTy.fix_isFixedPt {A : PartOrd} {L : LatTy}
    (f : [A]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) (a : [A]ᵈ) :
    f (a, (LatTy.fix f).hom a) = (LatTy.fix f).hom a := by
  have h := iterate_bot_stabilize
    (L := 〚L〛) (f := ⟨fun x => f (a, x), fun _ _ hxy => f.hom.monotone ⟨rfl, hxy⟩⟩)
    L.card (by rw [L.nat_card_eq])
  exact h

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
  | (.none, e) :: _ =>
    List.filter_eq_self.mp h (.none, e) List.mem_cons_self
      |> Bool.false_ne_true
      |>.elim

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
    prod_lift f g
  | prod_elim₁ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ fst
  | prod_elim₂ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ snd
  | abs_intro e A B he =>
    curry_left 〚show ((.none, A) :: Γ) ⊢ e : B from he〛
  | abs_elim e₁ e₂ A B he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : A.arr B from he₁〛
    let g := 〚show Γ ⊢ e₂ : A from he₂〛
    prod_lift g f ≫ ev
  | coprod_intro₁ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁ from he〛 ≫ inl
  | coprod_intro₂ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₂ from he〛 ≫ inr
  | coprod_elim e e₁ e₂ A₁ A₂ C he he₁ he₂ =>
    let f := 〚show Γ ⊢ e : A₁.coprod A₂ from he〛
    let g₁ := 〚show ((.none, A₁) :: Γ) ⊢ e₁ : C from he₁〛
    let g₂ := 〚show ((.none, A₂) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ dist.hom ≫ coprod_desc g₁ g₂
  | disc_intro e A he =>
    drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : A from he〛]ᵈ
  | disc_elim e₁ e₂ A C he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : [A]ᵈ from he₁〛
    let g := 〚show ((.D, A) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ g
  | bot_intro L => PartOrd.terminal.from 〚Γ〛 ≫ LatTy.bot L
  | one_intro e T he =>
    drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : T.toTy from he〛]ᵈ ≫ (T.toTy_denotation ▸ one)
  | sup_intro e₁ e₂ L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : L from he₁〛
    let g := 〚show Γ ⊢ e₂ : L from he₂〛
    prod_lift f g ≫ LatTy.sup L
  | for_intro e₁ e₂ T L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : 𝒫 T from he₁〛
    let g := 〚show ((.D, T.toTy) :: Γ) ⊢ e₂ : L from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ LatTy.comprehension L (T.toTy_denotation ▸ g)
  | fix_intro e L he =>
    let f := 〚show ((.none, L) :: [Γ]ᵈ) ⊢ e : L from he〛
    drop Γ ≫ δ [Γ]ᵈ ≫ LatTy.fix ((disc.comonad.ε.app 〚[Γ]ᵈ〛 ⊗ₘ 𝟙 〚L〛) ≫ f)

end Datafun
