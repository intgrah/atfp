module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Data.Sum.Order
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Category.Semilat

@[expose] public section

/-! Definition 4.3.1 -/

namespace PartOrd

open CategoryTheory Limits MonoidalCategory

universe u

variable {A B C D : PartOrd.{u}}

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
  ofHom ⟨nofun, nofun⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => ext nofun)

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

def dist {A B C : PartOrd.{u}} : A ⊗ (B.coprod C) ≅ (A ⊗ B).coprod (A ⊗ C) where
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

def ev : A ⊗ A.exp B ⟶ B :=
  ofHom {
    toFun := fun (a, f) => f.hom a
    monotone' := fun (_, f₁) (a₂, _) ⟨ha, hf⟩ =>
      (f₁.hom.monotone ha).trans (hf a₂)
  }

def coev : B ⟶ A.exp (A ⊗ B) :=
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
  coev ≫ (expFunctor B).map (prod_lift snd fst ≫ f)

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
  map {X Y} f := @ofHom [X]ᵈ [Y]ᵈ _ _ ⟨f, fun _ _ => congrArg f⟩
  ε.app X := @ofHom [X]ᵈ X _ _ ⟨id, fun | _, _, rfl => le_rfl⟩
  δ.app X := @ofHom [X]ᵈ [[X]ᵈ]ᵈ _ _ ⟨id, fun _ _ h => h⟩

notation "[" f "]ᵈ" => disc.comonad.map f

def iso_terminal : [𝟙_ PartOrd]ᵈ ≅ 𝟙_ PartOrd where
  hom := @ofHom [𝟙_ PartOrd]ᵈ _ _ _ ⟨id, fun _ _ _ => le_rfl⟩
  inv := @ofHom _ [𝟙_ PartOrd]ᵈ _ _ ⟨id, fun _ _ _ => rfl⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

def iso_prod (X Y : PartOrd) : [X ⊗ Y]ᵈ ≅ [X]ᵈ ⊗ [Y]ᵈ where
  hom := @ofHom [X ⊗ Y]ᵈ _ _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mp h)⟩
  inv := @ofHom _ [X ⊗ Y]ᵈ _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mpr h)⟩
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

abbrev U.bot (L : SemilatSupCat) : 𝟙_ PartOrd ⟶ U.obj L :=
  ofHom ⟨fun _ => ⊥, fun _ _ _ => le_rfl⟩

abbrev U.sup (L : SemilatSupCat) : U.obj L ⊗ U.obj L ⟶ U.obj L :=
  ofHom ⟨fun (x, y) => x ⊔ y, fun _ _ ⟨hx, hy⟩ => sup_le_sup hx hy⟩

abbrev one {X : PartOrd} : [X]ᵈ ⟶ of (Set X) :=
  ofHom (X := [X]ᵈ) {
    toFun x := ({x} : Set X)
    monotone' := by intro _ _ rfl; rfl
  }

end PartOrd
