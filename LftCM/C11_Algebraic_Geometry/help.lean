import Lean.Elab.Command

/-
# Custom `#help`, `#tactics` and `#lemmas` tactics/commands

This file does not contain any exercise.
The helper commands are simply accessed by typing `#help`, `#tactics` or `#lemmas` either as
commands, in-between declarations, or
inside tactic-mode.
They show an alphabetical listing of tactics and lemmas/defs used
in the proposed solutions to the exercises.
-/

namespace Tactic.Suggestions

open Lean

/-- Convert a comma-separated `Sting` into a `MessageData`. -/
def toMessageData (s type : String) : MessageData :=
let tacArr := m!"{s.splitOn ","}"
m!"Possibly useful {type}:{indentD tacArr}"

/--  The path to the file with the information about `tactics` and `lemmas`. -/
def cheat : System.FilePath :=
  "LftCM/C11_Algebraic_Geometry/helpData.txt"

/--  Produces the message depending on whether the input is `tactics`, `lemmas` or anything else. -/
def tacsOrLems (s : Option (TSyntax `str)) : IO MessageData := do
  if let #[_, lems, tacs] := ← IO.FS.lines cheat then
    match s.getD default with
      | `("tactics") => return toMessageData tacs "tactics"
      | `("lemmas")  => return toMessageData lems "lemmas"
      | _            => return toMessageData tacs "tactics" ++ "\n\n" ++ toMessageData lems "lemmas"
  else return "No info available"

/-- Typing `#help`, `#tactics` or `#lemmas` shows some hints. -/
syntax (name := helpC) "#help" (colGt str)? : command
@[inherit_doc helpC]
syntax (name := helpT) "#help" (colGt str)? : tactic

elab_rules : command | `(command| #help $[$str]?) => do logInfo (← tacsOrLems str)
elab_rules : tactic  | `(tactic|  #help $[$str]?) => do logInfo (← tacsOrLems str)

@[inherit_doc helpC] macro "#tactics" : command => `(command| #help "tactics")
@[inherit_doc helpC] macro "#lemmas"  : command => `(command| #help "lemmas")

@[inherit_doc helpC] macro "#tactics" : tactic  => `(tactic|  #help "tactics")
@[inherit_doc helpC] macro "#lemmas"  : tactic  => `(tactic|  #help "lemmas")

end Tactic.Suggestions
