-- import Compose.Class
import Compose.Lawful

namespace Hidden

abbrev Comp (T₁ T₂ : Type → Type) (α : Type) := T₁ (T₂ α)

instance [F₁ : Functor T₁] [F₂ : Functor T₂] : Functor (Comp T₁ T₂) where
  map := F₁.map ∘ F₂.map

instance [Functor T₁] [Functor T₂] [LawfulFunctor T₁] [LawfulFunctor T₂] :
    LawfulFunctor (Comp T₁ T₂) where
  id_map := by
    intro _ x
    show map (map id) x = x
    rw [show map id = id from by exact funext id_map]
    exact id_map _

  comp_map := by
    intro _ _ _ f g x
    show map (map f) (map (map g) x) = map (map (f ∘ g)) x
    simp
    rw [show map f ∘ map g = map (f ∘ g) from by funext; simp]

instance [F₁ : Applicative T₁] [F₂ : Applicative T₂] : Applicative (Comp T₁ T₂) where
  pure := F₁.pure ∘ F₂.pure
  seq f x := F₁.seq (F₁.seq (F₁.pure F₂.seq) f) x

instance [F₁ : Applicative T₁] [Applicative T₂] [LawfulApplicative T₁] [LawfulApplicative T₂] :
    LawfulApplicative (Comp T₁ T₂) where
  id_pure := by
    intro _ x
    show pure (· <*> ·) <*> pure (pure id) <*> x = x
    simp
    rw [show (fun y => y) = id from rfl]
    exact id_pure _

  map_pure := by
    intro _ _ f x
    show pure (· <*> ·) <*> pure (pure f) <*> pure (pure x) = pure (pure (f x))
    simp [map_pure]

  seq_pure := by
    intro _ _ x y
    show pure (· <*> ·) <*> x <*> pure (pure y) = pure (· <*> ·) <*> pure (pure (· y)) <*> x
    rw [seq_pure]
    simp
    guard_target =ₛ pure ((· (pure y)) ∘ (· <*> ·)) <*> x = pure (pure (· y) <*> ·) <*> x

    rw [congrArg (fun f => F₁.pure f)]
    show (· <*> pure y) = (pure (· y) <*> ·)

    ext
    exact seq_pure _ _

  seq_assoc := by
    intro _ _ _ x y z
    show
      pure (· <*> ·) <*> x <*> (pure (· <*> ·) <*> y <*> z) =
        pure (· <*> ·) <*> (
          pure (· <*> ·) <*> (
            pure (· <*> ·) <*> pure (pure (· ∘ ·)) <*> x
          ) <*> y
        ) <*> z
    simp
    rw [seq_pure]
    simp only [map_pure, seq_assoc]
    guard_target =ₛ
      pure ((· (· <*> ·)) ∘ (· ∘ ·) ∘ (· ∘ ·) ∘ (· <*> ·)) <*> x <*> y <*> z =
        pure (((· <*> ·) ∘ ·) ∘ (· <*> ·) ∘ (pure (· ∘ ·) <*> ·)) <*> x <*> y <*> z

    rw [congrArg (fun f => F₁.pure f <*> x <*> y <*> z)]
    show (fun u v w => u <*> (v <*> w)) = (fun u v w => pure (· ∘ ·) <*> u <*> v <*> w)

    ext
    exact seq_assoc _ _ _
