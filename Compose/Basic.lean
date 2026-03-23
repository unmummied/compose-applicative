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
  mySeq_myPure (x : T (α → β)) (y : α) :
    x <*> myPure y = myPure (· <| y) <*> x

  /-- The composition law of Applicative -/
  mySeq_assoc (x : T (β → γ)) (y : T (α → β)) (z : T α) :
    x <*> (y <*> z) = myPure (· ∘ ·) <*> x <*> y <*> z

open LawfulMyApplicative

@[simp]
theorem myPure_mySeq
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
      rw [id_myPure]

    · intros _ _ _ g g' y
      show myPure g <*> (myPure g' <*> y) = myPure (g ∘ g') <*> y
      exact this _ _ _

  exact (uniq_myMap F.toMyFunctor F' L.toLawfulMyFunctor L' _ _).symm

@[simp]
theorem shortcut
    [F : MyApplicative T] [L : LawfulMyApplicative T]
    (f : β → γ) (g : α → β) (x : T α) :
    myPure f <*> (myPure g <*> x) = myPure (f ∘ g) <*> x := by
  rw [mySeq_assoc]
  repeat rw [myMap_myPure]

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
    rw [id_myMap]

  comp_myMap := by
    intros _ _ _ f g x
    show myMap (myMap f) (myMap (myMap g) x) = myMap (myMap (f ∘ g)) x
    rw [comp_myMap]
    rw [show myMap f ∘ myMap g = myMap (f ∘ g) from by exact funext (comp_myMap _ _)]

instance [F : MyApplicative T] [F' : MyApplicative T'] :
    MyApplicative (MyComp T T') where
  myPure x := F.myPure (F'.myPure x)
  mySeq f x := F.mySeq (F.mySeq (F.myPure F'.mySeq) f) x

instance
    [F : MyApplicative T] [F' : MyApplicative T']
    [L : LawfulMyApplicative T] [L' : LawfulMyApplicative T'] :
    LawfulMyApplicative (MyComp T T') where
  id_myPure := by
    intros _ x
    show myPure (· <*> ·) <*> myPure (myPure id) <*> x = x
    rw [myMap_myPure]
    simp [myPure_mySeq, id_myMap]
    rw [show (fun y => y) = id from by exact List.map_inj.mp rfl]
    rw [id_myMap]

  myMap_myPure := by
    intros _ _ f x
    show
      myPure (· <*> ·) <*> (myPure (myPure f)) <*> (myPure (myPure x)) =
        myPure (myPure (f x))
    repeat rw [myMap_myPure]

  mySeq_myPure := by
    intros α β x y
    show
      myPure (· <*> ·) <*> x <*> myPure (myPure y) =
        myPure (· <*> ·) <*> myPure (myPure (· y)) <*> x
    rw [mySeq_myPure, myMap_myPure, shortcut]
    simp [myPure_mySeq]

    show myMap ((· (myPure y)) ∘ (· <*> ·)) x = myMap (myMap (· y) ·) x
    rw [congrArg (fun f : T' (α → β) → T' β => myMap f x)]

    show (fun z : T' (α → β) => z <*> myPure y) = (myMap (· y) ·)
    ext _
    rw [mySeq_myPure, myPure_mySeq]

  mySeq_assoc := by
    intros β γ α x y z
    show
      myPure (· <*> ·) <*> x <*> (myPure (· <*> ·) <*> y <*> z) =
        myPure (· <*> ·) <*> (
          myPure (· <*> ·) <*> (
            myPure (· <*> ·) <*> myPure (myPure (· ∘ ·)) <*> x
          ) <*> y
        ) <*> z
    rw [myMap_myPure]
    simp only [mySeq_assoc, myMap_myPure]
    rw [mySeq_myPure, shortcut]

    show
      myPure ((· (· <*> ·)) ∘ (· ∘ ·) ∘ (· ∘ ·) ∘ (· <*> ·)) <*> x <*> y <*> z =
        myPure (((· <*> ·) ∘ ·) ∘ (· <*> ·) ∘ (myPure (· ∘ ·) <*> ·)) <*> x <*> y <*> z

    rw [congrArg (fun f : T' (β → γ) → T' (α → β) → T' α → T' γ => myPure f <*> x <*> y <*> z)]
    show
      (fun u v w => u <*> (v <*> w)) = (fun u v w => myPure (· ∘ ·) <*> u <*> v <*> w)

    ext _ _ _
    exact mySeq_assoc _ _ _

example {α : Type} {t : Type → Type}
    (f : (α → α) → t α → t α)
    (h : ∀ (y : t α), f id y = y) : f id = id := by
  exact funext h
