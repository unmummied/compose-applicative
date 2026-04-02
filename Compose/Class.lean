namespace Hidden

class Functor (T : Type → Type) where
  map : (α → β) → T α → T β

export Functor (map)

class Applicative (T : Type → Type) extends Functor T where
  pure : α → T α
  seq : T (α → β) → T α → T β

export Applicative (pure seq)

infixl:60 (priority := high) " <*> " => seq
