class MyFunctor (T : Type → Type) where
  myMap : (α → β) → T α → T β

open MyFunctor

class LawfulMyFunctor (T : Type → Type) [MyFunctor T] where
  /-- The identity law of Functor -/
  id_myMap (x : T α) :
    myMap id x = x

  /-- The composition law of Functor -/
  comp_myMap (f : β → γ) (g : α → β) (x : T α) :
    myMap f (myMap g x) = myMap (f ∘ g) x

open LawfulMyFunctor
attribute [simp] id_myMap
attribute [simp] comp_myMap

/-- Uniqueness of map -/
axiom uniq_myMap
    (F F' : MyFunctor T)
    (L : @LawfulMyFunctor _ F) (L' : @LawfulMyFunctor _ F')
    (f : α → β) (x : T α) :
  F.myMap f x = F'.myMap f x

class MyApplicative (T : Type → Type) extends MyFunctor T where
  myPure : α → T α
  mySeq : T (α → β) → T α → T β

open MyApplicative
infixl:60 (priority:=high) " <*> " => mySeq

class LawfulMyApplicative
    (T : Type → Type) [MyApplicative T] extends LawfulMyFunctor T where
  /-- The identity law of Applicative -/
  id_myPure (x : T α) :
    myPure id <*> x = x

  /-- The homomorphism law of Applicative -/
  myMap_myPure (f : α → β) (x : α) :
    myPure f <*> (myPure x : T α) = myPure (f x)

  /-- The interchange law of Applicative -/
  mySeq_pure (x : T (α → β)) (y : α) :
    x <*> myPure y = myPure (· <| y) <*> x

  /-- The composition law of Applicative -/
  mySeq_assoc (x : T (β → γ)) (y : T (α → β)) (z : T α) :
    x <*> (y <*> z) = myPure (· ∘ ·) <*> x <*> y <*> z

open LawfulMyApplicative
attribute [simp] id_myPure
attribute [simp] myMap_myPure
attribute [simp] mySeq_pure
attribute [simp] mySeq_assoc

@[simp]
theorem pure_seq
    [F : MyApplicative T] [L : LawfulMyApplicative T]
    (f : α → β) (x : T α) :
    myPure f <*> x = myMap f x := by

  have {α β γ} (g : β → γ) (g' : α → β) (y : T α) :
      myPure g <*> (myPure g' <*> y) = myPure (g ∘ g') <*> y := by
    simp only [myMap_myPure, mySeq_assoc]

  let F' : MyFunctor T := ⟨(myPure · <*> ·)⟩
  have L' : @LawfulMyFunctor _ F' := by
    constructor

    · intros _ x'
      show myPure id <*> x' = x'
      simp

    · intros _ _ _ g g' y
      show myPure g <*> (myPure g' <*> y) = myPure (g ∘ g') <*> y
      exact this _ _ _

  exact (uniq_myMap F.toMyFunctor F' L.toLawfulMyFunctor L' _ _).symm

def MyComp (T T' : Type → Type) (α : Type) := T (T' α)

instance [F : MyFunctor T] [F' : MyFunctor T'] :
    MyFunctor (MyComp T T') where
  myMap f x := F.myMap (F'.myMap f) x

instance
    [F : MyFunctor T] [F' : MyFunctor T']
    [L : LawfulMyFunctor T] [L' : LawfulMyFunctor T'] :
    LawfulMyFunctor (MyComp T T') where
  id_myMap := by
    intros _ x
    show myMap (myMap id) x = x
    rw [show myMap id = id from by exact funext id_myMap]
    simp

  comp_myMap := by
    intros _ _ _ f g x
    show myMap (myMap f) (myMap (myMap g) x) = myMap (myMap (f ∘ g)) x
    simp only [comp_myMap]
    rw [show myMap f ∘ myMap g = myMap (f ∘ g) from by exact funext (comp_myMap _ _)]
