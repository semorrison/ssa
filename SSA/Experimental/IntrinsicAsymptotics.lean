-- Investigations on asymptotic behavior of representing programs with large explicit contexts

/-- A very simple type universe. -/
inductive Ty
  | nat
  | bool
  deriving DecidableEq, Repr

def Ty.toType
  | nat => Nat
  | bool => Bool

inductive Value where
  | nat : Nat → Value
  | bool : Bool → Value
  deriving Repr, Inhabited

abbrev State := List Value

/-- A context is a list of types, growing to the left for simplicity. -/
abbrev Ctxt := List Ty

/-- A very simple intrinsically typed expression. -/
inductive IExpr : Ctxt → Ty → Type
  /-- Variables are represented as indices into the context, i.e. `var 0` is the most recently introduced variable. -/
  | add (a : Fin Γ.length) (b : Fin Γ.length): IExpr Γ .nat
  /-- Nat literals. -/
  | nat (n : Nat) : IExpr Γ .nat
  deriving Repr

/-- A very simple intrinsically typed program: a sequence of let bindings. -/
inductive ICom : List Ty → Ty → Type where
  | ret (e : IExpr Γ α) : ICom Γ α
  | let (e : IExpr Γ α) (body : ICom (α :: Γ) β) : ICom Γ β
  deriving Repr

set_option profiler true
set_option pp.proofs.withType false  -- hide `Fin` statements

-- A simple first program
-- Observation: without the type annotation, we accumulate an exponentially large tree of nested contexts and `List.get`s.
-- By repeatedly referring to the last variable in the context, we force proof (time)s to grow linearly, resulting in
-- overall quadratic elaboration times.
def ex: ICom [] .nat :=
  ICom.let (.nat 0) <|
  ICom.let (α := .nat) (.add ⟨0, by decide⟩ ⟨0, by decide⟩) <|
  ICom.let (α := .nat) (.add ⟨1, by decide⟩ ⟨1, by decide⟩) <|
  ICom.let (α := .nat) (.add ⟨2, by decide⟩ ⟨2, by decide⟩) <|
  ICom.let (α := .nat) (.add ⟨3, by decide⟩ ⟨3, by decide⟩) <|
  ICom.let (α := .nat) (.add ⟨4, by decide⟩ ⟨4, by decide⟩) <|
  ICom.let (α := .nat) (.add ⟨5, by decide⟩ ⟨5, by decide⟩) <|
  ICom.ret (.add ⟨0, by decide⟩ ⟨0, by decide⟩)

def get_nat : Value → Nat := sorry 

def IExpr.denote : IExpr l ty → (ll : State) → (l.length = ll.length) → Value 
| .nat n, _, _ => .nat n
| .add a b, ll, h => let a_val : Nat := get_nat (ll.get (Fin.mk a (h ▸ a.isLt)))
                     let b_val : Nat := get_nat (ll.get (Fin.mk a (h ▸ a.isLt)))
                     Value.nat (a_val + b_val)

def ICom.denote : ICom l ty → (ll : State) → (l.length = ll.length) →  Value
| .ret e, l, h => e.denote l h
| .let e body, l, h => body.denote ((e.denote l h) :: l) (by simp [h])

-- let's automate
macro "mk_lets" n:num init:term : term =>
  n.getNat.foldRevM (fun n stx => `(ICom.let (α := .nat) (.var ⟨$(Lean.quote n), by decide⟩) $stx)) init

macro "mk_com" n:num : term =>
`(show ICom [] .nat from
  ICom.let (.nat 0) <|
  mk_lets $n
  ICom.ret (.var ⟨0, by decide⟩))

macro "mk_ex" n:num : command =>
`(theorem t : ICom [] .nat :=
  mk_com $n)

-- type checking took 146ms
-- elaboration took 327ms
mk_ex 50
-- type checking took 574ms
-- elaboration took 1.41s
mk_ex 100
-- type checking took 911ms
-- elaboration took 2.26s
mk_ex 120

-- Clearly not linear!

-- Apart from proving transformations of specific (sub)programs, we are also interested in applying such
-- verified transformations to larger programs parsed at run time.

/-- An untyped expression as an intermediate step of input processing. -/

abbrev Var := Nat
inductive Expr : Type
  | add (a : Var) (b : Var)
  | nat (n : Nat)
  deriving Repr, Inhabited

inductive LeafVar : Type
  | a
  | b
  | c
deriving Repr, Inhabited, DecidableEq


inductive ExprRec : Type
  | add (a : ExprRec) (b : ExprRec)
  | nat (n : Nat)
  | var (idx : LeafVar)
  deriving Repr, Inhabited

/-- An untyped command; types are always given as in MLIR. -/
inductive Com : Type where
  | let (ty : Ty) (e : Expr) (body : Com) : Com
  | ret (e : Var) : Com

def ex' : Com :=
  Com.let .nat (.nat 0) <|
  Com.let .nat (.add 0 0) <|
  Com.let .nat (.add 1 0) <|
  Com.let .nat (.add 2 0) <|
  Com.let .nat (.add 3 3) <|
  Com.let .nat (.add 4 4) <|
  Com.let .nat (.add 5 5) <|
  Com.ret 0

open Lean in 

def formatCom : Com → Nat → Std.Format
  | .ret v, _=> "\n.ret " ++ (repr v)
  | .let ty e body, n=> "\n.let " ++ (repr ty) ++ " " ++ (repr e) ++ (formatCom body n)

instance : Repr Com where
  reprPrec :=  formatCom

abbrev Mapping := List (LeafVar × Var)
abbrev Lets := Array Expr

def ex0 : Com :=
  Com.let .nat (.nat 0) <|
  Com.let .nat (.add 0 0) <|
  Com.let .nat (.add 1 0) <|
  Com.let .nat (.add 2 0) <|
  Com.let .nat (.add 3 0) <|
  Com.ret 0

-- a + b => b + a
def m := ExprRec.add (.var .a) (.var .b)
def r := ExprRec.add (.var .b) (.var .a)
def r2 := ExprRec.add (.var .b) (.add (.var .a) (.var .a))
def r3 := ExprRec.add (.add (.var .a) (.var .a)) (.var .b)
def r4 := ExprRec.add (.add (.var .b) (.var .b)) (.var .a)

def matchVar' (lets : Lets) (varPos: Nat) (matchExpr: ExprRec) (mapping: Mapping): Option Mapping := do
  let var := lets[varPos]!
  match var, matchExpr with
    | .add a b, .add a' b' => 
        let mapping ← match a' with
          | .var x => (x, varPos - 1 - a)::mapping
          | _=>  matchVar' lets (varPos - a - 1) a' mapping
        match b' with
          | .var x => (x, varPos - 1 - b)::mapping
          | _=>  matchVar' lets (varPos - b - 1) a' mapping
    | _, _ => none 

def matchVar (lets : Lets) (varPos: Nat) (matchExpr: ExprRec) : Option Mapping := 
  matchVar' lets varPos matchExpr [] 
  
#eval ex0
#eval matchVar (#[.nat 0, .add 0 0, .add 1 0, .add 2 0, .add 3 0]) 4 m

def getVarAfterMapping (var : LeafVar) (m : Mapping) : Nat :=
 match m with
 | x :: xs => if var = x.1 then
                 x.2
              else
                 getVarAfterMapping var xs
 | _ => panic! "var should be in mapping"

def applyMapping  (pattern : ExprRec) (m : Mapping) (lets : Lets): Lets := 
match pattern with
    | .var _ => lets
    | .add a b => 
      let lets := applyMapping a m lets
      let lets := applyMapping b m lets
      let l := match a with
        | .var s => getVarAfterMapping s m 
        | _ => lets.size
      let l := lets.size - l - 1
      let r := match b with
        | .var s => getVarAfterMapping s m
        | _ => lets.size
      let r := lets.size - r - 1
      lets.push (Expr.add l r)
    | .nat n => lets.push (Expr.nat n)

def replaceUsesOfVar (inputProg : Com) (var_pos: Nat) (new : Var) : Com :=
  inputProg

def addLetsToProgram (newLets : Lets) (n : Nat) (newProgram : Com) : Com :=
  match n with
  | 0 => newProgram
  | (x + 1) => if x < newLets.size then
                 let added := Com.let .nat (newLets.get! x) newProgram
                 addLetsToProgram newLets x (added)
               else
                 newProgram

def applyRewrite (lets : Lets) (inputProg : Com) (rewrite: ExprRec × ExprRec) : Option Com := do
  let varPos := lets.size - 1 
  let mapping ← matchVar lets varPos rewrite.1
  let lets := applyMapping (rewrite.2) mapping lets
  let newProgram := inputProg
  let newProgram := addLetsToProgram lets (lets.size) newProgram

  some newProgram

def rewriteAt (inputProg : Com) (depth : Nat) (lets: Lets) (rewrite: ExprRec × ExprRec) : Option Com :=
  match inputProg with
    | .ret _ => none
    | .let _ expr body =>
        let lets := lets.push expr
        if depth = 0 then
           applyRewrite lets body rewrite
        else
           rewriteAt body (depth - 1) lets rewrite

#eval rewriteAt ex0 4 #[] (m, r4)

  
  




def Expr.denote : Expr → State → Value
| .nat n, _ => .nat n
| .add a b, l => let a_val := get_nat (l.get! a)
                 let b_val := get_nat (l.get! b)
                 Value.nat (a_val + b_val)

def Com.denote : Com → State → Value
| .ret _ e, l => e.denote l
| .let _ e body, l => denote body ((e.denote l) :: l)


macro "mk_lets'" n:num init:term : term =>
  n.getNat.foldRevM (fun n stx => `(Com.let .nat (.add $(Lean.quote n) $(Lean.quote n)) $stx)) init

macro "mk_com'" n:num : term =>
`(Com.let .nat (.nat 0) <|
  mk_lets' $n
  Com.ret .nat (.add 0 0))

macro "mk_ex'" n:num : command =>
`(theorem t : Com :=
  mk_com' $n)

-- just for comparison, creating untyped terms takes insignificant time
mk_ex' 50
mk_ex' 100
set_option maxRecDepth 10000 in
mk_ex' 1000

-- Stubs of the desired program pipeline

def parse : String → Except String Com := sorry

def check : Com → Except String (Σ ty, ICom [] ty) := go []
where
  go (Γ : Ctxt) : Com → Except String (Σ ty, ICom Γ ty)
    | .ret ty e => do
      let e ← checkExpr Γ ty e
      return ⟨ty, .ret e⟩
    | .let ty e body => do
      let e ← checkExpr Γ ty e
      let ⟨ty, body⟩ ← go (ty :: Γ) body
      return ⟨ty, .let e body⟩
  checkExpr (Γ : Ctxt) : (ty : Ty) → Expr → Except String (IExpr Γ ty)
    | .nat, .nat n => .ok (.nat n)
    | .bool, .nat _ => .error "type error"
    | ty,   .add a b =>
      if h : a < Γ.length && b < Γ.length then
        let v_a : Fin Γ.length := ⟨v_a, h⟩
        if h_a : ty = Γ.get v_a then h ▸ .ok (.add v_a v_b) else .error "type error"
      else .error "var error"

set_option pp.proofs true in
set_option profiler.threshold 10
#reduce check ex'
#eval check ex'

-- run-time execution should still be quadratic because of `List.get`
#eval check (mk_com' 100)
#eval check (mk_com' 200)
#eval check (mk_com' 300)
#eval check (mk_com' 400)

def transform : ICom [] ty → ICom [] ty := sorry
def denote : ICom [] ty → ty.toType := sorry
def print : ICom [] ty → String := sorry

-- The big theorem; `parse/check/print` are probably not interesting to verify,
-- except to show that `check` does not change the program.
theorem td : denote (transform c) = denote c := sorry

def main (args : List String) : IO Unit := do
  let p ← IO.FS.readFile args[0]!
  let p ← IO.ofExcept (parse p)
  let ⟨_ty, p⟩ ← IO.ofExcept (check p)
  IO.print (print (transform p))
