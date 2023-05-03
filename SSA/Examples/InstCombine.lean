import SSA.WellTypedFramework
import Aesop

namespace InstCombine

abbrev Width := { x : Nat // 0 < x } -- difference with { x : Nat  | 0 < x }?
abbrev BitVector (w : Width) := Fin (2^w)
inductive BaseType
| bitvec (w : Width) : BaseType

instance : Goedel BaseType where
toType := fun
  | .bitvec w => BitVector w

abbrev UserType := SSA.UserType BaseType

-- See: https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
inductive Op
| and (w : Width) : Op
| or (w : Width) : Op
| xor (w : Width) : Op
| shl (w : Width) : Op
| lshr (w : Width) : Op
| ashr (w : Width) : Op
deriving Repr, DecidableEq

-- Can we get rid of the code repetition here? (not that copilot has any trouble completing this)
@[reducible]
def argUserType : Op → UserType
| Op.and w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))
| Op.or w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))
| Op.xor w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))
| Op.shl w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))
| Op.lshr w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))
| Op.ashr w => .pair (.base (BaseType.bitvec w)) (.base (BaseType.bitvec w))

def outUserType : Op → UserType
| Op.and w => .base (BaseType.bitvec w)
| Op.or w => .base (BaseType.bitvec w)
| Op.xor w => .base (BaseType.bitvec w)
| Op.shl w => .base (BaseType.bitvec w)
| Op.lshr w => .base (BaseType.bitvec w)
| Op.ashr w => .base (BaseType.bitvec w)

def rgnDom : Op → UserType := sorry
def rgnCod : Op → UserType := sorry

def BitVector.and : ∀ {w : Width}, BitVector w → BitVector w → BitVector w := (· &&& ·)
def BitVector.or : ∀ {w : Width}, BitVector w → BitVector w → BitVector w := (· ||| ·)
def BitVector.xor : ∀ {w : Width}, BitVector w → BitVector w → BitVector w := (· ^^^ ·)

theorem Nat.zero_lt_pow {m n : Nat} : (0 < n) → 0 < n^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro h
    rw [Nat.pow_succ]
    exact Nat.mul_pos (ih h) h

theorem Width.zero_lt_pow_2 {w : Width} : 0 < 2^w.val := by
  have h : 0 < 2 := Nat.zero_lt_succ 1
  exact @Nat.zero_lt_pow w.val 2 h

def Width.nat_pow (n : Nat) (w : Width) : Nat :=
 n ^ w

theorem Nat.gt_of_lt {a b : Nat} : a < b → b > a := by simp

def _root_.Nat.asBitVector (n : Nat) {w : Width} : BitVector w :=
  { val := n % (2^w), isLt := (Nat.mod_lt n w.zero_lt_pow_2) }

def BitVector.shl {w : Width} (op₁ op₂ : BitVector w) : BitVector w :=
 op₁.val * (2^op₂.val) |>.asBitVector

def BitVector.lshr {w : Width} (op₁ op₂ : BitVector w) : BitVector w := op₁ >>> op₂
def BitVector.ashr {w : Width} (op₁ op₂ : BitVector w) : BitVector w := op₁ >>> op₂ -- not capturing the difference here obviously
def BitVector.shl' {w : Width} (op₁ op₂ : BitVector w) : BitVector w := op₁ <<< op₂


def eval : ∀ (o : Op), Goedel.toType (argUserType o) → (Goedel.toType (rgnDom o) →
  Goedel.toType (rgnCod o)) → Goedel.toType (outUserType o) :=
  fun o arg _ => match o, arg with
    | Op.and w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.and x y
    | Op.or w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.or x y
    | Op.xor w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.xor x y
    | Op.lshr w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.lshr x y
    | Op.ashr w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.ashr x y
    | Op.shl w, SSA.UserType.pair x y => fun (x y : BitVector w) => UserType.base $ BitVector.shl x y

instance : SSA.TypedUserSemantics Op BaseType where
argUserType := argUserType
rgnDom := rgnDom
rgnCod := rgnCod
outUserType := outUserType
eval := eval

/-
Optimization: InstCombineShift: 239
%Op0 = shl %X, C
%r = lshr %Op0, C
=>
%r = and %X, (-1 u>> C)
-/
end InstCombine
