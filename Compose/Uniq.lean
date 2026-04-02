import Compose.Lawful

namespace Hidden

axiom uniq_map
  (_ : @LawfulFunctor T F₁) (_ : @LawfulFunctor T F₂)
  (f : α → β) (v : T α) : F₁.map f v = F₂.map f v

theorem pure_seq
    [Applicative T] [L : LawfulApplicative T] (f : α → β) (x : T α) :
    pure f <*> x = map f x := by

  let F' : Functor T := ⟨(pure · <*> ·)⟩
  have L' : @LawfulFunctor T F' := by
    constructor

    · intro _ x'
      show pure id <*> x' = x'
      exact id_pure _

    · intro _ _ _ g₁ g₂ y
      show pure g₁ <*> (pure g₂ <*> y) = pure (g₁ ∘ g₂) <*> y
      simp

  exact (uniq_map L.toLawfulFunctor L' _ _).symm
