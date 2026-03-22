namespace Hidden

class Functor (t : Type → Type) where
  map : (α → β) → t α → t β

open Functor
notation "map" => Functor.map

class LawfulFunctor (t : Type → Type) [Functor t] where
  /-- The identity law of Functor -/
  id_map (x : t α) :
    map id x = x

  /-- The composition law of Functor -/
  comp_map (f : β → γ) (g : α → β) (x : t α) :
    map f (map g x) = map (f ∘ g) x

open LawfulFunctor
notation "id_map"   => LawfulFunctor.id_map
notation "comp_map" => LawfulFunctor.comp_map

/-- Uniqueness of map -/
axiom uniq_map
    (F₁ F₂ : Functor t)
    (L₁ : @LawfulFunctor _ F₁) (L₂ : @LawfulFunctor _ F₂)
    (f : α → β) (x : t α) :
  @Functor.map _ F₁ _ _ f x = @Functor.map _ F₂ _ _ f x

class Applicative (t : Type → Type) extends Functor t where
  pure : α → t α
  seq : t (α → β) → t α → t β

open Applicative
notation "pure" => Applicative.pure
notation "seq"  => Applicative.seq
infixl:60 (priority:=high) " <*> " => Applicative.seq

class LawfulApplicative (t : Type → Type) [Applicative t] extends LawfulFunctor t where
  /-- The identity law of Applicative -/
  id_pure (x : t α) :
    pure id <*> x = x

  /-- The homomorphism law of Applicative -/
  map_pure (f : α → β) (x : α) :
    pure f <*> (pure x : t α) = pure (f x)

  /-- The interchange law of Applicative -/
  seq_pure (x : t (α → β)) (y : α) :
    x <*> pure y = pure (· <| y) <*> x

  /-- The composition law of Applicative -/
  seq_assoc (x : t (β → γ)) (y : t (α → β)) (z : t α) :
    x <*> (y <*> z) = pure (· ∘ ·) <*> x <*> y <*> z

open LawfulApplicative
notation "map_pure"  => LawfulApplicative.map_pure
notation "seq_pure"  => LawfulApplicative.seq_pure
notation "seq_assoc" => LawfulApplicative.seq_assoc

theorem pure_seq [F : Applicative t] [L : LawfulApplicative t] (f : α → β) (x : t α) :
    pure f <*> x = map f x := by

  have {α β γ} (g₁ : β → γ) (g₂ : α → β) (y : t α) :
      pure g₁ <*> (pure g₂ <*> y) = pure (g₁ ∘ g₂) <*> y := by
    calc
      _ = pure (· ∘ ·) <*> pure g₁ <*> pure g₂ <*> y := by rw [seq_assoc]
      _ = pure (g₁ ∘ g₂) <*> y                       := by rw [map_pure, map_pure]

  -- let an another implementation of map for t
  let F' : Functor t := Functor.mk (pure · <*> ·)
  have L' : @LawfulFunctor _ F' := by
    refine ⟨?_, ?_⟩

    · intro α x'
      show pure id <*> x' = x'
      rw [id_pure]

    · intro β γ α g₁ g₂ y
      show pure g₁ <*> (pure g₂ <*> y) = pure (g₁ ∘ g₂) <*> y
      exact this _ _ _

  exact (uniq_map F.toFunctor F' L.toLawfulFunctor L' _ _).symm

end Hidden
