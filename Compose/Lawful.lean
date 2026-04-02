import Compose.Class

namespace Hidden

class LawfulFunctor (T : Type → Type) [Functor T] where
  id_map (x : T α) : map id x = x
  comp_map (f : β → γ) (g : α → β) (x : T α) : map f (map g x) = map (f ∘ g) x

export LawfulFunctor (id_map comp_map)
attribute [simp] id_map
attribute [simp] comp_map

class LawfulApplicative (T : Type → Type) [Applicative T] extends LawfulFunctor T where
  id_pure (v : T α) : pure id <*> v = v
  map_pure (f : α → β) (x : α) : pure f <*> (pure x : T α) = pure (f x)
  seq_pure (u : T (α → β)) (y : α) : u <*> pure y = pure (· y) <*> u
  seq_assoc (u : T (β → γ)) (v : T (α → β)) (w : T α) :
    u <*> (v <*> w) = pure (· ∘ ·) <*> u <*> v <*> w

export LawfulApplicative (id_pure map_pure seq_pure seq_assoc)
attribute [simp] id_pure
attribute [simp] map_pure
attribute [simp] seq_assoc
