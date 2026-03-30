namespace Hidden

class Functor (T : Type → Type) where
  map : (α → β) → T α → T β

export Functor (map)

class LawfulFunctor (T : Type → Type) [Functor T] where
  id_map (x : T α) :
    map id x = x

  comp_map (f : β → γ) (g : α → β) (x : T α) :
    map f (map g x) = map (f ∘ g) x

export LawfulFunctor (id_map comp_map)
attribute [simp] id_map
attribute [simp] comp_map

axiom uniq_map
  (_ : @LawfulFunctor T F₁) (_ : @LawfulFunctor T F₂)
  (f : α → β) (v : T α) : F₁.map f v = F₂.map f v

class Applicative (T : Type → Type) extends Functor T where
  pure : α → T α
  seq : T (α → β) → T α → T β

export Applicative (pure seq)
infixl:60 (priority := high) " <*> " => seq

class LawfulApplicative (T : Type → Type) [Applicative T] extends LawfulFunctor T where
  id_pure (v : T α) :
    pure id <*> v = v

  map_pure (f : α → β) (x : α) :
    pure f <*> (pure x : T α) = pure (f x)

  seq_pure (u : T (α → β)) (y : α) :
    u <*> pure y = pure (· y) <*> u

  seq_assoc (u : T (β → γ)) (v : T (α → β)) (w : T α) :
    u <*> (v <*> w) = pure (· ∘ ·) <*> u <*> v <*> w

export LawfulApplicative (id_pure map_pure seq_pure seq_assoc)
attribute [simp] id_pure
attribute [simp] map_pure
attribute [simp] seq_assoc

theorem pure_seq [Applicative T] [L : LawfulApplicative T]
    (f : α → β) (x : T α) : pure f <*> x = map f x := by

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

theorem pure_seq_pure_seq
    [Applicative T] [LawfulApplicative T]
    (f : β → γ) (g : α → β) (x : T α) :
    pure f <*> (pure g <*> x) = pure (f ∘ g) <*> x := by
  simp

def Comp (T₁ T₂ : Type → Type) (α : Type) := T₁ (T₂ α)

instance [F₁ : Functor T₁] [F₂ : Functor T₂] :
    Functor (Comp T₁ T₂) where
  map f x := F₁.map (F₂.map f) x

instance
    [Functor T₁] [Functor T₂]
    [LawfulFunctor T₁] [LawfulFunctor T₂] :
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

instance [F₁ : Applicative T₁] [F₂ : Applicative T₂] :
    Applicative (Comp T₁ T₂) where
  pure x := F₁.pure (F₂.pure x)
  seq f x := F₁.seq (F₁.seq (F₁.pure F₂.seq) f) x

instance
    [F₁ : Applicative T₁] [F₂ : Applicative T₂]
    [L₁ : LawfulApplicative T₁] [L₂ : LawfulApplicative T₂] :
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
    rw [pure_seq_pure_seq]
    guard_target =ₛ
      pure ((· (· <*> ·)) ∘ (· ∘ ·) ∘ (· ∘ ·) ∘ (· <*> ·)) <*> x <*> y <*> z =
        pure (((· <*> ·) ∘ ·) ∘ (· <*> ·) ∘ (pure (· ∘ ·) <*> ·)) <*> x <*> y <*> z

    rw [congrArg (fun f => F₁.pure f <*> x <*> y <*> z)]
    show (fun u v w => u <*> (v <*> w)) = (fun u v w => pure (· ∘ ·) <*> u <*> v <*> w)

    ext
    exact seq_assoc _ _ _

end Hidden
