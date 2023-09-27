import SSA.Projects.MLIRSyntax.Parser
import SSA.Projects.InstCombine.LLVM.Transform
import Init.Data.Repr

open MLIR AST

def regionTransform (region : Region) : Except ParseError 
  (Σ (Γ' : Context) (ty : InstCombine.Ty), Com Γ' ty) :=  
  let res := mkCom region
  match res with 
    | Except.error e => Except.error s!"Error:\n{reprStr e}" 
    | Except.ok res => Except.ok res

unsafe def regionElab : Lean.Syntax → Lean.Elab.Term.TermElabM (Option Region) := 
fun stx => elabInto `MLIR.AST.Region stx

unsafe def regionElabAndTransform : Lean.Syntax → Lean.Elab.TermElabM (Option (Σ (Γ' : Context) (ty : InstCombine.Ty), Com Γ' ty)) := 
fun stx => do
  let elaborated? ←  regionElab stx
  match elaborated? with
    | none => return none
    | some elaborated =>
      let transformed := regionTransform elaborated
      match transformed with
        | Except.error e => return none
        | Except.ok transformed => return transformed

unsafe def regionParserFun : @ParseFun (Σ (Γ' : Context) (ty : InstCombine.Ty), Com Γ' ty) := 
  mkParseFun `mlir_region regionElabAndTransform