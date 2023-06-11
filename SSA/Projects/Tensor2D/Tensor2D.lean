import SSA.Core.WellTypedFramework
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import SSA.Core.Util


/-- Tensor2d with existential dimension sizes. -/
structure Tensor2d' (α : Type) where
  n₀ : ℕ
  n₁ : ℕ
  mat : Matrix (Fin n₀) (Fin n₁) α

def Tensor2d'.error (α : Type) : Tensor2d' α where
  n₀ := 0
  n₁ := 0
  mat := Matrix.of fun x _y => x.elim0

def Tensor2d'.transpose (t : Tensor2d' α) : Tensor2d' α where
  n₀ := t.n₁
  n₁ := t.n₀
  mat := t.mat.transpose

theorem Tensor2d'.transpose_transpose (t : Tensor2d' α) : t.transpose.transpose = t := rfl

def Tensor2d'.map (f : α → β) (t : Tensor2d' α) : Tensor2d' β where
  n₀ := t.n₀
  n₁ := t.n₁
  mat := t.mat.map f

theorem Tensor2d'.map_functorial (g : β → γ) (f : α → β) (t : Tensor2d' α) : t.map (g ∘ f) = (t.map f).map g := rfl

theorem Tensor2d'.map_error (f : α → β) : (Tensor2d'.error α).map f = Tensor2d'.error β := by {
  simp[map, error]
}
/-- K combinator / constant function. -/
def const (a : α) (_b : β) : α := a

def Tensor2d'.fill (v : β) (t : Tensor2d' α) : Tensor2d' β := t.map (const v)

/-- extract a submatrix of (sz₀ × sz₁) size at offset (δ₀, δ₁). Fails if this is out of bounds. -/
def Tensor2d'.extract (δ₀ δ₁ : ℕ) (sz₀ sz₁ : ℕ) (t : Tensor2d' α) : (Tensor2d' α) :=
  if SZ0 : δ₀ + sz₀ ≤ t.n₀ then
    if SZ1 : δ₁ + sz₁ ≤ t.n₁ then
      {
        n₀ := sz₀,
        n₁ := sz₁,
        mat := Matrix.of fun (ix₀ : Fin sz₀) (ix₁ : Fin sz₁) =>
          have INBOUNDS0 : δ₀ + ix₀ < t.n₀ := by linarith[ix₀.isLt]
          have INBOUNDS1 : δ₁ + ix₁ < t.n₁ := by linarith[ix₁.isLt]
          t.mat ⟨δ₀ + ix₀, INBOUNDS0⟩ ⟨δ₁ + ix₁, INBOUNDS1⟩
        : Tensor2d' α
      }
    else Tensor2d'.error (α := α)
  else Tensor2d'.error (α := α)

/-- This implies fill_extract -/
theorem Tensor2d'.map_extract (δ₀ δ₁ sz₀ sz₁ : ℕ) (t : Tensor2d' α) (f : α → β) :
  (t.map f).extract δ₀ δ₁ sz₀ sz₁ = (t.extract δ₀ δ₁ sz₀ sz₁).map f := by {
    simp only [extract];
    have MAP_n₀ : (map f t).n₀ = t.n₀ := rfl
    simp only [MAP_n₀]
    have MAP_n₁ : (map f t).n₁ = t.n₁ := rfl
    simp only [MAP_n₁]
    by_cases H₀ : δ₀ + sz₀ ≤ t.n₀ <;> simp[H₀, Tensor2d'.map_error];
    by_cases H₁ : δ₁ + sz₁ ≤ t.n₁ <;> simp[H₁, Tensor2d'.map_error];
    simp only [map, Matrix.map, Matrix.of_apply, Int.ofNat_add_ofNat, Eq.ndrec, Int.rawCast, Int.cast_id,
      Nat.rawCast, Nat.cast_id, Int.ofNat_eq_coe, eq_mp_eq_cast, id_eq]
}

theorem Tensor2d'.fill_extract (δ₀ δ₁ sz₀ sz₁ : ℕ) (t : Tensor2d' α) (v : β) :
  (t.fill v).extract δ₀ δ₁ sz₀ sz₁ = (t.extract δ₀ δ₁ sz₀ sz₁).fill v := by {
    simp only[fill, Tensor2d'.map_extract]
}


inductive Op
| add
-- TODO: generalize 'const'
| constNat (v: Nat) | constTensor (t : Tensor2d' Int) | constInt (v : Int)
| sub
| map2d
| fill2d
| extract2d 

inductive BaseType
| int : BaseType
| nat : BaseType
| tensor2d : BaseType
deriving DecidableEq, Inhabited

def BaseType.toType : BaseType → Type
| .int => Int
| .nat => Nat
| .tensor2d => Tensor2d' Int -- TODO: eventually generalize to arbitrary type.

instance : Goedel BaseType where toType := BaseType.toType

abbrev UserType := SSA.UserType BaseType

-- Can we get rid of the code repetition here? (not that copilot has any trouble completing this)
@[simp]
def argUserType : Op → UserType
| Op.add => ↑(BaseType.int, BaseType.int)
| Op.sub => ↑(BaseType.int, BaseType.int)
| Op.constNat _  => ()
| Op.constTensor _  => ()
| Op.constInt _  => ()
| Op.map2d => BaseType.tensor2d
| Op.fill2d => (BaseType.int, BaseType.tensor2d)
| Op.extract2d => (((BaseType.nat, BaseType.nat), (BaseType.nat, BaseType.nat)), BaseType.tensor2d)

@[simp]
def outUserType : Op → UserType
| Op.add => BaseType.int
| Op.sub => BaseType.int
| Op.constNat _ => BaseType.nat 
| Op.constTensor _ => BaseType.tensor2d
| Op.constInt _ => BaseType.int
| Op.map2d | Op.fill2d => BaseType.tensor2d
| Op.extract2d => BaseType.tensor2d

@[simp]
def rgnDom : Op → UserType
| Op.add | Op.sub | Op.fill2d | Op.extract2d  => .unit
| Op.constNat _ | Op.constTensor _ | Op.constInt _ => .unit
| Op.map2d => BaseType.int

@[simp]
def rgnCod : Op → UserType
| Op.add | Op.sub | Op.fill2d  | Op.extract2d => .unit
| Op.constNat _ | Op.constTensor _ | Op.constInt _ => .unit
| Op.map2d => BaseType.int

def eval (o : Op)
  (arg: Goedel.toType (argUserType o))
  (_rgn : (Goedel.toType (rgnDom o) → (Goedel.toType (rgnCod o)))) :
  (Goedel.toType (outUserType o)) :=
  match o with
  | .constNat v => v
  | .constTensor v => v
  | .constInt v => v
  | .add => 
    let (x, y) := arg;
    let x : Int := x;
    let y : Int := y;
    x + y
  | .sub =>
    let (x, y) := arg;
    let x : Int := x;
    let y : Int := y;
    x - y
  | .map2d => 
    let t : Tensor2d' Int := arg
    let f : Int → Int := _rgn -- FAILS.
    t.map f
  | .fill2d => 
    let (v, t) : Int × Tensor2d' Int  := arg
    t.fill v
  | .extract2d => 
    let ((δ, sz), t) := arg
    t.extract δ.fst δ.snd sz.fst sz.snd
    
instance TUS : SSA.TypedUserSemantics Op BaseType where
  argUserType := argUserType
  rgnDom := rgnDom
  rgnCod := rgnCod
  outUserType := outUserType
  eval := eval

syntax "map2d" : dsl_op2
syntax "fill2d" : dsl_op2
syntax "extract2d" : dsl_op2
syntax "constNat" "(" term ")" : dsl_op2
syntax "constTensor" "(" term ")" : dsl_op2
syntax "constInt" "(" term ")" : dsl_op2

open EDSL2 in
macro_rules
| `([dsl_op2| map2d]) => `(Op.map2d)
| `([dsl_op2| fill2d]) => `(Op.fill2d)
| `([dsl_op2| extract2d]) => `(Op.extract2d)
| `([dsl_op2| constNat($t)]) => `(Op.constNat $t)
| `([dsl_op2| constTensor($t)]) => `(Op.constTensor $t)
| `([dsl_op2| constInt($t)]) => `(Op.constInt $t)


-- Why do these not get set?
register_simp_attr SSA.teval
register_simp_attr EnvU.set
-- register_simp_attr Op.const
register_simp_attr argUserType
register_simp_attr eval
register_simp_attr outUserType
-- register_simp_attr BitVector.width
register_simp_attr uncurry

-- NOTE: there is no way in MLIR to talk about composition of functions, so `map . map` is out
--       as a peephole rewrite


-- TODO: enable not writing the unit argument if not used.
-- TOTHINK: See that there is no way to 
open SSA EDSL2 in
theorem map_fill_2d 
    (t : Tensor2d' Int)
    (sz₀ sz₁ ix₀ ix₁: Nat) 
    (i : Int):
  TSSA.eval
  (e := e) (Op := Op) (β := BaseType) [dsl_bb2|
    return op:fill2d (op:constInt(i) (), 
      op:extract2d (
          ((op:constNat(sz₀) () , op:constNat(sz₁) ()),
           (op:constNat(ix₀) (), op:constNat(ix₁) ())),
           op:constTensor(t) ()))
  ] =
  TSSA.eval (e := e) (Op := Op) (β := BaseType) [dsl_bb2|
    return op:extract2d 
      (((op:constNat(sz₀) (), op:constNat(sz₁) ()),
        (op:constNat(ix₀) (), op:constNat(ix₁) ())),
        op:fill2d (op:constInt(i) (), op:constTensor(t) ()))
  ] := by {
    dsimp only[TSSAIndex.eval, TSSA.eval]
    simp[UserType.mkPair, TypedUserSemantics.eval, eval]
    simp[Tensor2d'.fill_extract]
  }