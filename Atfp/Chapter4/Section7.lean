module

public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum

import Atfp.Chapter4.Section1
public import Atfp.Chapter4.Section4.Datafun
public import Atfp.Chapter4.Section6

@[expose] public section

namespace Datafun

open CategoryTheory MonoidalCategory

universe u

open Change

set_option hygiene false in
notation "〚" A "〛" => FinTy.denotationC A

def FinTy.denotationC : FinTy.{u} → Change.{u}
  | 1 => 𝟙_ Change
  | prod T₁ T₂ => 〚T₁〛 ⊗ 〚T₂〛
  | coprod T₁ T₂ => 〚T₁〛.coprod 〚T₂〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛.X)
  | discrete T => [〚T〛]ᵈ

set_option hygiene false in
notation "〚" A "〛" => Ty.denotationC A

noncomputable def Ty.denotationC : Ty.{u} → Change.{u}
  | 1 => 𝟙_ Change
  | prod A B => 〚A〛 ⊗ 〚B〛
  | arr A B => 〚A〛.exp 〚B〛
  | coprod A B => 〚A〛.coprod 〚B〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛.X)
  | discrete A => [〚A〛]ᵈ

lemma FinTy.toTy_denotationC {T : FinTy.{u}} :〚T〛 = 〚T.toTy〛 := by
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

instance LatTy.instSemilatticeSupC : (L : LatTy) → SemilatticeSup 〚L〛.X
  | unit => inferInstanceAs (SemilatticeSup PUnit)
  | prod L₁ L₂ => @Prod.instSemilatticeSup _ _ L₁.instSemilatticeSupC L₂.instSemilatticeSupC
  | powerset T => inferInstanceAs (SemilatticeSup (Set 〚T〛.X))

noncomputable instance LatTy.instOrderBotC : (L : LatTy) → OrderBot 〚L〛.X
  | unit => inferInstanceAs (OrderBot PUnit)
  | prod L₁ L₂ => @Prod.instOrderBot _ _ _ _ L₁.instOrderBotC L₂.instOrderBotC
  | powerset T => inferInstanceAs (OrderBot (Set 〚T〛.X))

noncomputable def LatTy.botC : (L : LatTy) → Change.terminal ⟶ 〚L〛
  | .unit => Change.terminal.from _
  | .prod L₁ L₂ =>
    prod_lift (Change.terminal.from _ ≫ L₁.botC) (Change.terminal.from _ ≫ L₂.botC)
  | .powerset _ => Change.bot

noncomputable def LatTy.supC : (L : LatTy) → 〚L〛.prod 〚L〛 ⟶ 〚L〛
  | .unit => Change.terminal.from _
  | .prod L₁ L₂ => tensor_exchange.hom ≫ prod_lift
      (fst ≫ supC L₁) (snd ≫ supC L₂)
  | .powerset _ => Change.sup

noncomputable def LatTy.comprehensionC {𝕏 : Change} {T : FinTy} :
    (L : LatTy) → (𝕏 ⊗ ([〚T〛]ᵈ) ⟶ 〚L〛) →
      (𝕏 ⊗ 〚𝒫 T〛 ⟶ 〚L〛)
  | .unit, _ => Change.terminal.from _
  | .prod L₁ L₂, f =>
    prod_lift (L₁.comprehensionC (f ≫ fst)) (L₂.comprehensionC (f ≫ snd))
  | .powerset T', f => {
      base := PartOrd.ofHom
        { toFun := fun (a, (s : Set 〚T〛.X)) =>
            (⋃ x ∈ s, f.base (a, x) : Set 〚T'〛.X)
          monotone' := by
            intro (a₁, (s₁ : Set 〚T〛.X)) (a₂, (s₂ : Set 〚T〛.X)) ⟨ha, hs⟩
            apply Set.iUnion₂_subset
            intro x hx₁
            have h₁ : f.base (a₁, x) ≤ f.base (a₂, x) := f.base.hom.monotone ⟨ha, le_rfl⟩
            have h₂ : f.base (a₂, x) ≤ ⋃ y ∈ s₂, f.base (a₂, y) :=
              Set.subset_biUnion_of_mem (u := fun y => f.base (a₂, y)) (hs hx₁)
            exact h₁.trans h₂ }
      hasDeriv := by
        obtain ⟨f', hf'⟩ := f.hasDeriv
        refine ⟨fun (a, (s : Set 〚T〛.X)) => PartOrd.ofHom
          ⟨fun ((da, (ds : Set 〚T〛.X)) : 𝕏.Δ a × Set 〚T〛.X) =>
            ((⋃ x ∈ s ∪ ds, f' (a, x) (da, ⟨⟩)) ∪ ⋃ x ∈ ds, f.base (a, x)
              : Set 〚T'〛.X),
          fun (da₁, ds₁) (da₂, ds₂) ⟨hda, hds⟩ => by
            apply Set.union_subset_union
            · apply Set.iUnion₂_subset
              intro x hx
              exact ((f' (a, x)).hom.monotone (show (da₁, (⟨⟩ : PUnit)) ≤ (da₂, ⟨⟩) from
                ⟨hda, le_rfl⟩)).trans
                (Set.subset_biUnion_of_mem (u := fun x => (f' (a, x)) (da₂, ⟨⟩))
                  (Set.union_subset_union_right s hds hx))
            · exact Set.iUnion₂_subset fun x hx =>
                (Set.subset_biUnion_of_mem (u := fun x => f.base (a, x)) (hds hx))⟩,
          fun (a, (s : Set 〚T〛.X))
              ((da, (ds : Set 〚T〛.X)) : 𝕏.Δ a × Set 〚T〛.X) => ?_⟩
        change (⋃ x ∈ s ∪ ds, f.base (a ⨁[𝕏] da, x) : Set 〚T'〛.X) =
          (⋃ x ∈ s, f.base (a, x)) ∪
            ((⋃ x ∈ s ∪ ds, f' (a, x) (da, ⟨⟩)) ∪ ⋃ x ∈ ds, f.base (a, x))
        ext y
        simp only [Set.mem_iUnion, Set.mem_union]
        apply Iff.intro
        · rintro ⟨x, hx | hx, hy⟩ <;> {
            have eq : f.base (a ⨁[𝕏] da, x) =
                (f.base (a, x) ∪ f' (a, x) (da, ⟨⟩) : Set 〚T'〛.X) :=
              hf' (a, x) (da, ⟨⟩)
            rw [eq, Set.mem_union] at hy
            rcases hy with hy | hy
            · first | exact .inl ⟨x, ‹_›, hy⟩ | exact .inr (.inr ⟨x, ‹_›, hy⟩)
            · exact .inr (.inl ⟨x, by tauto, hy⟩) }
        · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
          · exact ⟨x, .inl hx, f.base.hom.monotone
              (show ((a, x) : 𝕏.X × [〚T〛]ᵈ.X) ≤ (a ⨁[𝕏] da, x) from
                ⟨𝕏.update_monotone a da, rfl⟩) hy⟩
          · have eq := hf' (a, x) (da, ⟨⟩)
            dsimp [Change.prod, Change.disc] at eq
            exact ⟨x, hx.elim .inl .inr, eq ▸ .inr hy⟩
          · exact ⟨x, .inr hx, f.base.hom.monotone
              (show ((a, x) : 𝕏.X × [〚T〛]ᵈ.X) ≤ (a ⨁[𝕏] da, x) from
                ⟨𝕏.update_monotone a da, rfl⟩) hy⟩
    }

instance FinTy.instFiniteC : ∀ T : FinTy, Finite 〚T〛.X
  | unit => Finite.of_fintype PUnit
  | prod T₁ T₂ => @Finite.instProd 〚T₁〛.X 〚T₂〛.X T₁.instFiniteC T₂.instFiniteC
  | coprod T₁ T₂ => @Finite.instSum 〚T₁〛.X 〚T₂〛.X T₁.instFiniteC T₂.instFiniteC
  | powerset T => @Set.instFinite 〚T〛.X T.instFiniteC
  | discrete T => T.instFiniteC

instance LatTy.instFiniteC : ∀ L : LatTy, Finite 〚L〛.X
  | unit => Finite.of_fintype PUnit
  | prod L₁ L₂ => @Finite.instProd _ _ L₁.instFiniteC L₂.instFiniteC
  | powerset T => @Set.instFinite _ T.instFiniteC

noncomputable def LatTy.fixC {𝕏 : Change} {L : LatTy}
    (f : [𝕏]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) :
    [𝕏]ᵈ ⟶ 〚L〛 where
  base := @PartOrd.ofHom [𝕏]ᵈ.X 〚L〛.X _ _ {
    toFun a :=
      let f_a : 〚L〛.X →o 〚L〛.X :=
        ⟨fun x => f.base (a, x), fun _ _ hxy => f.base.hom.monotone ⟨rfl, hxy⟩⟩
      f_a^[L.card] (L.botC.base ⟨⟩)
    monotone' | _, _, rfl => le_rfl }
  hasDeriv :=
    ⟨fun _ => PartOrd.ofHom ⟨fun ⟨⟩ => 〚L〛.zero _, fun _ _ _ => le_rfl⟩,
      fun _ ⟨⟩ => (〚L〛.zero_update _).symm⟩

theorem FinTy.nat_card_eqC : ∀ T : FinTy, Nat.card 〚T〛.X = T.card
  | unit => by
    change Nat.card PUnit = 1
    simp [Nat.card_eq_fintype_card]
  | prod T₁ T₂ => by
    change Nat.card (〚T₁〛.X × 〚T₂〛.X) = T₁.card * T₂.card
    rw [Nat.card_prod, T₁.nat_card_eqC, T₂.nat_card_eqC]
  | coprod T₁ T₂ => by
    change Nat.card (〚T₁〛.X ⊕ 〚T₂〛.X) = T₁.card + T₂.card
    rw [@Nat.card_sum _ _ T₁.instFiniteC T₂.instFiniteC, T₁.nat_card_eqC, T₂.nat_card_eqC]
  | powerset T => by
    change Nat.card (Set 〚T〛.X) = 2 ^ T.card
    rw [show Set 〚T〛.X = (〚T〛.X → Prop) from rfl, @Nat.card_fun _ _ T.instFiniteC, T.nat_card_eqC]
    simp [Nat.card_eq_fintype_card]
  | discrete T => T.nat_card_eqC

theorem LatTy.nat_card_eqC : ∀ L : LatTy, Nat.card 〚L〛.X = L.card
  | unit => by
    change Nat.card PUnit = 1
    simp [Nat.card_eq_fintype_card]
  | prod L₁ L₂ => by
    change Nat.card (〚L₁〛.X × 〚L₂〛.X) = L₁.card * L₂.card
    rw [Nat.card_prod, L₁.nat_card_eqC, L₂.nat_card_eqC]
  | powerset T => by
    change Nat.card (Set 〚T〛.X) = 2 ^ T.card
    rw [show Set 〚T〛.X = (〚T〛.X → Prop) from rfl,
      @Nat.card_fun _ _ T.instFiniteC, T.nat_card_eqC]
    simp [Nat.card_eq_fintype_card]

theorem LatTy.fixC_isFixedPt {𝕏 : Change} {L : LatTy}
    (f : [𝕏]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) (a : [𝕏]ᵈ.X) :
    f.base (a, (L.fixC f).base a) = (L.fixC f).base a := by
  sorry

set_option hygiene false in
notation "〚" Γ "〛" => Ctx.denotationC Γ

noncomputable def Ctx.denotationC : Ctx.{u} → Change.{u}
  | [] => 𝟙_ Change
  | (.none, A) :: Γ => 〚Γ〛 ⊗ 〚A〛
  | (.D, A) :: Γ => 〚Γ〛 ⊗ [〚A〛]ᵈ

noncomputable def Ctx.lookupC {q A} :
    (Γ : Ctx) → (x : ℕ) → Γ[x]? = some (q, A) → (〚Γ〛 ⟶ 〚A〛)
  | (.none, A) :: Γ, 0, rfl => snd
  | (.none, _) :: Γ, x + 1, h => fst ≫ Ctx.lookupC Γ x h
  | (.D, A) :: Γ, 0, rfl => snd ≫ disc.comonad.ε.app 〚A〛
  | (.D, _) :: Γ, x + 1, h => fst ≫ Ctx.lookupC Γ x h

noncomputable def Ctx.dropC (Γ : Ctx) : 〚Γ〛 ⟶ 〚[Γ]ᵈ〛 :=
  match Γ with
  | [] => 𝟙 〚[]〛
  | (.none, _) :: Γ => fst ≫ Ctx.dropC Γ
  | (.D, A) :: Γ => Ctx.dropC Γ ⊗ₘ 𝟙 [〚A〛]ᵈ

lemma Ctx.disc.idem {Γ : Ctx} : [[Γ]ᵈ]ᵈ = [Γ]ᵈ := by
  let p : Qualifier × Ty → Bool := (· matches (.D, _))
  have := @List.filter_filter _ p p Γ
  simp [Ctx.disc]

noncomputable def Ctx.δC (Δ : Ctx)
    (h : [Δ]ᵈ = Δ := by exact Ctx.disc.idem) : 〚Δ〛 ⟶ [〚Δ〛]ᵈ :=
  match Δ with
  | [] => disc.iso_terminal.inv
  | (.D, A) :: Δ =>
    (Ctx.δC Δ (congrArg List.tail h) ⊗ₘ disc.comonad.δ.app 〚A〛) ≫
      (disc.iso_prod 〚Δ〛 [〚A〛]ᵈ).inv
  | (.none, e) :: _ =>
    List.filter_eq_self.mp h (.none, e) List.mem_cons_self
      |> Bool.false_ne_true
      |>.elim

set_option hygiene false in
notation "〚" h "〛" => HasType.denotationC h

open Ctx (dropC δC) in
noncomputable def HasType.denotationC {Γ e A} : (Γ ⊢ e : A) → (〚Γ〛 ⟶ 〚A〛)
  | var x A hx => Ctx.lookupC Γ x hx
  | dvar x A hx => Ctx.lookupC Γ x hx
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
    dropC Γ ≫ δC [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : A from he〛]ᵈ
  | disc_elim e₁ e₂ A C he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : [A]ᵈ from he₁〛
    let g := 〚show ((.D, A) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ g
  | bot_intro L => Change.terminal.from 〚Γ〛 ≫ LatTy.botC L
  | one_intro e T he =>
    dropC Γ ≫ δC [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : T.toTy from he〛]ᵈ ≫ (T.toTy_denotationC ▸ one)
  | sup_intro e₁ e₂ L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : L from he₁〛
    let g := 〚show Γ ⊢ e₂ : L from he₂〛
    prod_lift f g ≫ LatTy.supC L
  | for_intro e₁ e₂ T L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : 𝒫 T from he₁〛
    let g := 〚show ((.D, T.toTy) :: Γ) ⊢ e₂ : L from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ LatTy.comprehensionC L (T.toTy_denotationC ▸ g)
  | fix_intro e L he =>
    let f := 〚show ((.none, L) :: [Γ]ᵈ) ⊢ e : L from he〛
    dropC Γ ≫ δC [Γ]ᵈ ≫ LatTy.fixC ((disc.comonad.ε.app 〚[Γ]ᵈ〛 ⊗ₘ 𝟙 〚L〛) ≫ f)

end Datafun
