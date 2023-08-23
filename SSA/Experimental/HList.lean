import Mathlib.Tactic.Basic
import Mathlib.Tactic.LibrarySearch


inductive HList {α : Type*} (f : α → Type*) : List α → Type _
  | nil : HList f []
  | cons {a : α} : (f a) → HList f as → HList f (a :: as)

namespace HList

/-
  # Definitions
-/

def map {A B : α → Type*} (f : ∀ (a : α), A a → B a) :
    ∀ {l : List α}, HList A l → HList B l
  | [],   .nil        => .nil
  | t::_, .cons a as  => .cons (f t a) (map f as)

def foldl {A : α → Type*} {B : Type*} (f : ∀ (a : α), B → A a → B) :
    ∀ {l : List α}, B → HList A l → B
  | [],   b, .nil       => b
  | t::_, b, .cons a as => foldl f (f t b a) as

def get {as} : HList A as → (i : Fin as.length) → A (as.get i)
  | .nil, i => i.elim0
  | .cons x  _, ⟨0,   _⟩  => x
  | .cons _ xs, ⟨i+1, h⟩  => get xs ⟨i, Nat.succ_lt_succ_iff.mp h⟩

@[coe]
def toSingle {A : α → Type*} (xs : HList A [a₁]) : A a₁ :=
  xs.get (0 : Fin 1)

@[coe]
def toPair {A : α → Type*} (xs : HList A [a₁, a₂]) : A a₁ × A a₂ :=
  (xs.get (0 : Fin 2), xs.get (1 : Fin 2))

@[coe]
def toTriple {A : α → Type*} (xs : HList A [a₁, a₂, a₃]) : A a₁ × A a₂ × A a₃ :=
  (xs.get (0 : Fin 3), xs.get (1 : Fin 3), xs.get (2 : Fin 3))

/-
  # Theorems
-/

theorem map_map {A B C : α → Type*} {l : List α} (t : HList A l)
    (f : ∀ a, A a → B a) (g : ∀ a, B a → C a) :
    (t.map f).map g = t.map (fun a v => g a (f a v)) := by
  induction t <;> simp_all [map]

end HList