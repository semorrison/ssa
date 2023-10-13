import SSA.Projects.FullyHomomorphicEncryption.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.List.Basic 

variable {q t : Nat} [ hqgt1 : Fact (q > 1)] {n : Nat}
variable (a b : R q n)

namespace Poly 

theorem mul_comm : a * b = b * a := by
  ring

theorem add_comm : a + b = b + a := by
  ring

theorem f_eq_zero : (f q n) = (0 : R q n) := by
  apply Ideal.Quotient.eq_zero_iff_mem.2
  rw [Ideal.mem_span_singleton]

theorem mul_f_eq_zero : a * (f q n) = 0 := by
  rw [f_eq_zero]; ring

theorem mul_one_eq : 1 * a = a := by
  ring

theorem add_f_eq : a + (f q n) = a := by
  rw [← mul_one_eq (q := q) (n := n) (f q n), mul_f_eq_zero 1]; ring

theorem add_zero_eq : a + 0 = a := by
  ring

theorem eq_iff_rep_eq :a.representative = b.representative ↔ a = b := by 
  constructor
  · intros hRep
    have hFromPolyRep : R.fromPoly (q := q) (n := n) a.representative = R.fromPoly (q := q) (n := n) b.representative := by
      rw [hRep]
    rw [R.fromPoly_representative _ _ _ , R.fromPoly_representative _ _ _ ] at hFromPolyRep
    assumption
  · intro h; rw [h]

open Polynomial in
theorem from_poly_zero : R.fromPoly (0 : (ZMod q)[X]) (n := n) = (0 : R q n) := by
  have hzero : f q n * 0 = 0 := by simp
  rw [← hzero]
  apply R.fromPoly_kernel_eq_zero

theorem rep_zero : R.representative q n 0 = 0 := by
  rw [← from_poly_zero, R.representative_fromPoly]; simp


open Polynomial in
theorem monomial_mul_mul (x y : Nat) : (R.monomial 1 y) * (R.monomial 1 x) = R.monomial 1 (x + y) (q := q) (n := n) := by
  unfold R.monomial
  rw [← map_mul, monomial_mul_monomial, Nat.add_comm]
  simp

end Poly

theorem R.toTensor_length : a.toTensor.length = a.rep_length := by
  unfold R.toTensor
  unfold R.rep_length
  cases Polynomial.degree a.representative <;> simp


theorem R.toTensor_getD (i : Nat) : a.toTensor.getD i 0 = (a.coeff i).toInt := by 
  simp [R.toTensor, R.coeff]
  have hLength : (List.map (fun i => ZMod.toInt q (Polynomial.coeff (R.representative q n a) i)) (List.range (R.rep_length a))).length = rep_length a := by
    simp 
  by_cases (i < R.rep_length a) 
  · rw [← hLength] at h; rw [List.getD_eq_get _ _ h, List.get_map, List.get_range]
  · rw [Nat.not_lt] at h
    rw [List.getD_eq_default _, Polynomial.coeff_eq_zero_of_degree_lt]
    simp [ZMod.toInt]; rw [ZMod.toInt_zero (q := q)]
    unfold R.rep_length at h 
    cases hDeg : Polynomial.degree (R.representative q n a) 
    · apply WithBot.bot_lt_coe 
    · simp [hDeg] at h
      apply WithBot.some_lt_some.2
      apply h
    · rw [← hLength] at h
      apply h

theorem R.toTensor_getD' (i : Nat) : ↑(a.toTensor.getD i 0) = a.coeff i := by 
  rw [R.toTensor_getD]
  rw [ZMod.toInt_coe_eq]

theorem R.monomial_zero_c_eq_zero : R.monomial (q := q) (n := n) 0 c = 0 := by
  unfold R.monomial
  rw [Polynomial.monomial_zero_right]
  simp 

theorem R.fromTensor_eq_concat_zero (tensor : List Int) : 
  R.fromTensor (q := q) (n := n) tensor = R.fromTensor (q := q) (n := n) (tensor ++ [0]) := by
  unfold R.fromTensor
  simp
  rw [List.enum_append, List.enumFrom_singleton, List.foldl_concat]
  simp [R.monomial_zero_c_eq_zero]


theorem R.fromTensor_eq_concat_zeroes (tensor : List Int) (k : Nat) :
   R.fromTensor (q := q) (n := n) (tensor ++ List.replicate k 0) = R.fromTensor (q := q) (n := n) tensor := by
  induction k generalizing tensor with
   | zero => simp
   | succ k ih => 
       simp [ih]
       have H : tensor ++ (0 :: List.replicate k 0) = (tensor ++ [0]) ++ List.replicate k 0 := 
        List.append_cons ..
       rw[H]
       rw [ih (tensor ++ [0])]
       rw[← R.fromTensor_eq_concat_zero]

@[simp]
theorem R.trimTensor_append_zero_eq (tensor : List Int) :  trimTensor (tensor ++ [0]) = trimTensor tensor := by
  simp [trimTensor]
  rw [List.dropWhile]
  simp

@[simp]
theorem R.trimTensor_append_zeroes_eq (tensor : List Int) (n : Nat) :  trimTensor (tensor ++ List.replicate n 0) = trimTensor tensor := by
  induction n with 
  | zero => simp
  | succ n ih =>
     rw [List.replicate_succ', ← List.append_assoc, R.trimTensor_append_zero_eq,ih]

theorem R.trimTensor_append_not_zero (tensor : List Int) (x : Int) (hX : x ≠ 0) :
  trimTensor (tensor ++ [x]) = tensor ++ [x] := by
  simp [trimTensor]; rw [List.dropWhile]
  simp [hX]

theorem R.trimTensor_eq_append_zeros (tensor : List Int) : ∃ (n : Nat), 
tensor = trimTensor tensor ++ List.replicate n 0 := by
induction tensor using List.reverseRecOn with
   | H0 => exists 0 
   | H1 xs x ih =>
     have ⟨n,hxs⟩ := ih 
     by_cases (x = 0)
     · exists (n + 1)
       rw [h]
       simp
       rw [← List.replicate_succ, List.replicate_succ', ← List.append_assoc, ← hxs]
     · exists 0
       rw [R.trimTensor_append_not_zero _ _ h] ; simp

theorem R.trimTensor_getD_0 (tensor: List Int) : 
  tensor.getD i 0 = (trimTensor tensor).getD i 0 := by
  have ⟨n, H⟩ := trimTensor_eq_append_zeros tensor 
  conv =>
    lhs 
    rw[H]
  by_cases INBOUNDS:(i < List.length (trimTensor tensor))
  . rw[List.getD_append (h := INBOUNDS)]
  . have OUT_OF_BOUNDS : List.length (trimTensor tensor) ≤ i := by linarith
    rw[List.getD_eq_default (hn := OUT_OF_BOUNDS)]
    rw[List.getD_append_right (h := OUT_OF_BOUNDS)]
    rw[List.getD_replicate_default_eq]

theorem R.trimTensor_trimTensor (tensor : List Int) : 
  trimTensor (trimTensor tensor) = trimTensor tensor := by
  induction tensor using List.reverseRecOn with
    | H0 => simp
    | H1 xs x ih => 
       by_cases (x = 0)
       · rw [h, R.trimTensor_append_zero_eq,ih]
       · rw [trimTensor_append_not_zero _ _ h, trimTensor_append_not_zero _ _ h]

theorem R.fromTensor_eq_fromTensor_trimTensor (tensor : List Int) :
   R.fromTensor (q := q) (n := n) (trimTensor tensor) = R.fromTensor (q := q) (n := n) tensor := by
  have ⟨n,hn⟩ := R.trimTensor_eq_append_zeros tensor
  conv => 
    rhs 
    rw [hn]
  simp[R.fromTensor_eq_concat_zeroes]

namespace Poly

theorem eq_iff_coeff_eq : a = b ↔ Polynomial.coeff a.representative = Polynomial.coeff b.representative := by
  constructor
  .  intro h; rw [h]
  ·  intro h
     apply (eq_iff_rep_eq _ _).1
     apply Polynomial.coeff_inj.1
     exact h

theorem toTensor_length_eq_rep_length : 
  a.toTensor.length = a.rep_length := by
  simp [R.rep_length, R.toTensor]
    
theorem toTensor_trimTensor_eq_toTensor : 
  trimTensor a.toTensor = a.toTensor := by
  unfold R.toTensor
  cases h : Polynomial.degree a.representative with
  | none => simp [h, R.rep_length]
  | some n  => 
    simp [R.rep_length, h]
    rw [List.range_succ, List.map_append]
    simp
    have hNe := Polynomial.coeff_ne_zero_of_eq_degree h
    simp [R.coeff, hNe]
    have hNe': ZMod.toInt q (Polynomial.coeff (a.representative) n) ≠ 0 := by
      intro contra
      have contra' := (ZMod.toInt_zero_iff_zero _ _).2 contra
      contradiction
    apply R.trimTensor_append_not_zero  _ _ hNe'

theorem toTensor_fromTensor (tensor : List Int) (i : Nat): 
  (R.fromTensor tensor (q:=q) (n :=n)).toTensor.getD i 0 = tensor.getD i 0 := by
  by_cases (i < (trimTensor tensor).length)
  · sorry
  · sorry

theorem toTensor_fromTensor_trimTensor (tensor : List Int) {l : Nat}: 
  Polynomial.degree a.representative = .some l → tensor.length < l → 
  (R.fromTensor (trimTensor tensor) (q:=q) (n :=n)).toTensor = trimTensor tensor := by
  intros hDeg hLen
  --simp [R.fromTensor, R.toTensor]
  sorry

theorem toTensor_fromTensor' (tensor : List Int) {l : Nat}: 
  Polynomial.degree a.representative = .some l → tensor.length < l → 
  (R.fromTensor tensor (q:=q) (n :=n)).toTensor = trimTensor tensor := by
  intros hDeg hLen
  --simp [R.fromTensor, R.toTensor]
  have ⟨n,hTrim⟩ := R.trimTensor_eq_append_zeros tensor
  rw [hTrim,R.trimTensor_append_zeroes_eq, R.fromTensor_eq_concat_zeroes, R.trimTensor_trimTensor]
  apply toTensor_fromTensor_trimTensor _ _ hDeg hLen

theorem poly_fromTensor_toTensor : R.fromTensor a.toTensor = a := by
  cases h : Polynomial.degree (R.representative q n a) with
    | none => 
        have h' :=  Polynomial.degree_eq_bot.1 h
        rw [← rep_zero] at h'
        have h'':= (eq_iff_rep_eq _ _).1 h'
        simp [R.fromTensor, R.toTensor, R.rep_length]; rw [h, h'']
        simp
    | some deg =>
        apply (eq_iff_coeff_eq _ _).2
        have hCoeff := R.toTensor_getD' (q := q) (n := n)
        unfold R.coeff at hCoeff
        apply funext
        intro i
        rw [← hCoeff, ← hCoeff]
        rw [toTensor_fromTensor]

end Poly