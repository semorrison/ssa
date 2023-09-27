import SSA.Projects.MLIRSyntax.AST
import SSA.Projects.MLIRSyntax.EDSL
import Lean

open Lean
abbrev ParseOutput := String
abbrev ParseError := String
abbrev CheckerFun := String → Lean.Environment → Elab.Command.CommandElabM ParseOutput

def mkParseFun {α : Type} [ToString α] (syntaxcat : Name) 
  (ntparser : Syntax → Except ParseError α)
  (s : String) (env : Environment) : 
  Elab.Command.CommandElabM α := 
  IO.ofExcept <| Parser.runParserCategory env syntaxcat s >>= ntparser

-- Create a parser for a syntax category named `syntaxcat`, which uses `ntparser` to read a syntax node and produces a value α, or an error.
-- This returns a function that given a string `s` and an environment `env`, tries to parse the string, and produces an error.
private def mkNonTerminalParser {α : Type} [ToString α] (syntaxcat : Name) (ntparser : Syntax → Except ParseError α)
(s : String) (env : Environment) : Elab.Command.CommandElabM α :=
  let parseFun := mkParseFun syntaxcat ntparser
  parseFun s env


private def isFile (p: System.FilePath) : IO Bool := do
      return (<- p.metadata).type == IO.FS.FileType.file

private def checkFileParse (env: Lean.Environment)
  (checker: CheckerFun)
  (filepath: System.FilePath)
   : IO ParseOutput := do
  let lines <- IO.FS.lines filepath
  let fileStr := lines.foldl (λ s₁ s₂ => s₁ ++ "\n" ++ s₂) ""
  let parsed := checker fileStr env
  let runOnce := parsed.run {fileName := filepath.toString, fileMap := FileMap.ofString "", tacticCache? := .none}
  let runTwice := runOnce.run {env := env, maxRecDepth := defaultMaxRecDepth}
  match (runTwice .unit) with
    | .ok (ast, _) _ => return s!"{filepath}, ok, AST:\n{ast}"
    | .error e _ => do match e with
                        | .error ref msg => return s!"{filepath}, error {ref}\n{(← msg.toString)}"
                        | _ => return s!"{filepath}, internal error" -- should be unreachable

def runParser  (checker : CheckerFun) (fileName : String) : IO UInt32 := do
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let modules : List Import := [⟨`SSA.Projects.MLIRSyntax.EDSL, false⟩]
  let env ← importModules modules {}
  let filePath := System.mkFilePath [fileName]
  if !(← isFile filePath) then
    throw <| IO.userError s!"File {fileName} does not exist"
  let output ← checkFileParse env checker filePath 
  IO.println output
  return 0
