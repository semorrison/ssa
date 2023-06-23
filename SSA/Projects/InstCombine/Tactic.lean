import SSA.Core.WellTypedFramework
import SSA.Projects.InstCombine.InstCombineBase
import SSA.Projects.InstCombine.ForMathlib

open SSA 

macro "simp_alive": tactic =>
  `(tactic|
      (
        simp only [InstCombine.eval, pairMapM, pairBind, bind_assoc, pure,
                   Option.map, Option.bind_eq_some', Option.some_bind', Option.bind_eq_bind, 
                   Bitvec.Refinement.some_some]
      )
   )

