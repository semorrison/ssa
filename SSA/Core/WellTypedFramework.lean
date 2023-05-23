import SSA.Core.Framework
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.AList

/-- Typeclass for a `baseType` which is a Gödel code of
Lean types. -/
class Goedel (β : Type) : Type 1 where
  toType : β → Type
open Goedel /- make toType publically visible in module. -/

notation "⟦" x "⟧" => Goedel.toType x

instance : Goedel Unit where toType := fun _ => Unit

namespace SSA

/-- A `UserType` is a type of user-defined values in `SSA` programs.
    The main objective of `UserType` is to be able to have decidability
    properties, like decidable equality, for the restricted set of types
    in the user-defined semantics, since Lean's `Type` does not have these
    properties. -/
inductive UserType (β : Type) : Type where
  | base : β → UserType β
  | pair : UserType β → UserType β → UserType β
  | triple : UserType β → UserType β → UserType β → UserType β
  | unit : UserType β
  | region : UserType β → UserType β → UserType β
  deriving DecidableEq

namespace UserType

instance: Inhabited (UserType β) where default := UserType.unit

@[reducible]
def toType [Goedel β] : UserType β → Type
  | .base t =>  ⟦t⟧
  | .pair k₁ k₂ => (toType k₁) × (toType k₂)
  | .triple k₁ k₂ k₃ => toType k₁ × toType k₂ × toType k₃
  | .unit => Unit
  | .region k₁ k₂ => toType k₁ →toType k₂

instance [Goedel β] : Goedel (UserType β) where
  toType := toType

def mkPair [Goedel β] {k₁ k₂ : UserType β}: ⟦k₁⟧ → ⟦k₂⟧ → ⟦k₁.pair k₂⟧
  | k₁, k₂ => (k₁, k₂)

def mkTriple [Goedel β] {k₁ k₂ k₃ : UserType β}: ⟦k₁⟧ → ⟦k₂⟧ → ⟦k₃⟧ → ⟦k₁.triple k₂ k₃⟧
  | k₁, k₂, k₃ => (k₁, k₂, k₃)

def fstPair [Goedel β] {k₁ k₂ : UserType β} : ⟦k₁.pair k₂⟧ → ⟦k₁⟧
  | (k₁, _) => k₁

def sndPair [Goedel β] {k₁ k₂ : UserType β} : ⟦k₁.pair k₂⟧ → ⟦k₂⟧
  | (_, k₂) => k₂

def fstTriple [Goedel β] {k₁ k₂ k₃ : UserType β} : ⟦k₁.triple k₂ k₃⟧ → ⟦k₁⟧
  | (k₁, _, _) => k₁

def sndTriple [Goedel β] {k₁ k₂ k₃ : UserType β} : ⟦k₁.triple k₂ k₃⟧ → ⟦k₂⟧
  | (_, k₂, _) => k₂

def trdTriple [Goedel β] {k₁ k₂ k₃ : UserType β} : ⟦k₁.triple k₂ k₃⟧ → ⟦k₃⟧
  | (_, _, k₃) => k₃

end UserType



/-- Typeclass for a user semantics of `Op`, with base type `β`.
    The type β has to implement the `Goedel` typeclass, mapping into `Lean` types.
    This typeclass has several arguments that have to be defined to give semantics to
    the operations of type `Op`:
    * `argUserType` and `outUserType`, functions of type `Op → UserType β`, give the type of the
      arguments and the output of the operation.
    * `rgnDom` and `rgnCod`, functions of type `Op → UserType β`, give the type of the
      domain and codomain of regions within the operation.
    * `eval` gives the actual evaluation semantics of the operation, by defining a function for
      every operation `o : Op` of type `toType (argUserType o) → (toType (rgnDom o) → toType (rgnCod o)) → toType (outUserType o)`.
-/
class OperationTypes (Op : Type) (β : outParam Type) where
  argUserType : Op → UserType β
  rgnDom : Op → UserType β
  rgnCod : Op → UserType β
  outUserType : Op → UserType β

class TypedUserSemantics (Op : Type) (β : outParam Type) [Goedel β] extends OperationTypes Op β where
  eval : ∀ (o : Op), toType (argUserType o) → (toType (rgnDom o) →
    toType (rgnCod o)) → toType (outUserType o)

inductive Context (β : Type) : Type
  | empty : Context β
  | snoc : Context β → Var → (UserType β) → Context β

inductive Context.Var {β : Type} : Context β → UserType β → Type
  | prev {Γ : Context β} :
      Context.Var Γ a → Context.Var (Context.snoc Γ v' a') a
  | last {Γ : Context β} {v : SSA.Var} {a : UserType β} :
      Context.Var (Context.snoc Γ v a) a

instance {α : Type} : EmptyCollection (Context α) :=
  ⟨Context.empty⟩

def EnvC [Goedel β] (c : Context β)  :=
  ∀ ⦃a : UserType β⦄, c.Var a → ⟦a⟧

inductive TSSAIndex (β : Type) : Type
/-- LHS := RHS. LHS is a `Var` and RHS is an `SSA Op .EXPR` -/
| STMT : Context β → TSSAIndex β
/-- Ways of making an RHS -/
| EXPR : UserType β → TSSAIndex β
/-- The final instruction in a region. Must be a return -/
| TERMINATOR : UserType β → TSSAIndex β
/-- a lambda -/
| REGION : UserType β → UserType β → TSSAIndex β

@[simp]
def TSSAIndex.eval [Goedel β] : TSSAIndex β → Type
  | .STMT Γ => EnvC Γ
  | .EXPR T => toType T
  | .TERMINATOR T => toType T
  | .REGION dom cod => toType dom → toType cod

open OperationTypes UserType

inductive TSSA (Op : Type) {β : Type} [Goedel β] [OperationTypes Op β] :
    (Γ : Context β) → TSSAIndex β → Type where
  /-- lhs := rhs; rest of the program -/
  | assign {T : UserType β}
      (rest : TSSA Op Γ (.STMT Γ'))
      (lhs : Var) (rhs : TSSA Op Γ' (.EXPR T)) : TSSA Op Γ (.STMT (Γ'.snoc lhs T))
  /-- no operation. -/
  | nop : TSSA Op Γ (.STMT Γ)
  /-- above; ret v -/
  | ret (above : TSSA Op Γ (.STMT Γ')) (v : Γ'.Var T) : TSSA Op Γ  (.TERMINATOR T)
  /-- (fst, snd) -/
  | pair (fst : Γ.Var T₁) (snd : Γ.Var T₂) : TSSA Op Γ (.EXPR (.pair T₁ T₂))
  /-- (fst, snd, third) -/
  | triple (fst : Γ.Var T₁) (snd : Γ.Var T₂) (third : Γ.Var T₃) : TSSA Op Γ (.EXPR (.triple T₁ T₂ T₃))
  /-- op (arg) { rgn } rgn is an argument to the operation -/
  | op (o : Op) (arg : Γ.Var (argUserType o)) (rgn : TSSA Op Γ (.REGION (rgnDom o) (rgnCod o))) :
      TSSA Op Γ (.EXPR (outUserType o))
  /- fun arg => body -/
  | rgn {arg : Var} {dom cod : UserType β} (body : TSSA Op (Γ.snoc arg dom) (.TERMINATOR cod)) :
      TSSA Op Γ (.REGION dom cod)
  /- no function / non-existence of region. -/
  | rgn0 : TSSA Op Γ (.REGION unit unit)
  /- a region variable. --/
  | rgnvar (v : Γ.Var (.region T₁ T₂)) : TSSA Op Γ (.REGION T₁ T₂)
  /-- a variable. -/
  | var (v : Γ.Var T) : TSSA Op Γ (.EXPR T)

@[simp]
def TSSA.eval {Op β : Type} [Goedel β] [TUS : TypedUserSemantics Op β] :
  {Γ : Context β} → {i : TSSAIndex β} → TSSA Op Γ i → (e : EnvC Γ) → i.eval
| Γ, _, .assign rest lhs rhs => fun e T v =>
    match v with
    | Context.Var.prev v => rest.eval e v
    | Context.Var.last => rhs.eval (rest.eval e)
  | _, _, .nop => fun e => e
  | _, _, .ret above v => fun e => above.eval e v
  | _, _, .pair fst snd => fun e => mkPair (e fst) (e snd)
  | _, _, .triple fst snd third => fun e => mkTriple (e fst) (e snd) (e third)
  | _, _, TSSA.op o arg rg => fun e =>
    TypedUserSemantics.eval o (e arg) (rg.eval e)
  | _, _, .rgn body => fun e arg =>
      body.eval (fun _ v =>
        match v with
        | Context.Var.prev v' => e v'
        | Context.Var.last => arg)
  | _, _, .rgn0 => fun _ => id
  | _, _, .rgnvar v => fun e => e v
  | _, _, .var v => fun e => e v

-- We can recover the case with the TypeSemantics as an instance
def TypeSemantics : Type 1 :=
  ℕ → Type

inductive NatBaseType (TS : TypeSemantics) : Type
  | ofNat : ℕ → NatBaseType TS
deriving DecidableEq

instance : Goedel (NatBaseType TS) where toType :=
  fun n => match n with
    | .ofNat m => TS m

variable {TS : TypeSemantics}
abbrev NatUserType := UserType (NatBaseType TS)

end SSA

register_simp_attr Bind.bind
register_simp_attr Option.bind
register_simp_attr TypedUserSemantics.eval
register_simp_attr TypedUserSemantics.argUserType
register_simp_attr TypedUserSemantics.outUserType
register_simp_attr TypedUserSemantics.regionDom
register_simp_attr TypedUserSemantics.regionCod