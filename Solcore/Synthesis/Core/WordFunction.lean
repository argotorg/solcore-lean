import Solcore.Synthesis.Core.Fragment

/-! Checked scalar functions with one runtime Word input. This profile is
separate from the closed G0 program generator and does not change its version.
Literal abstraction creates candidates; the ordinary Core checker seals every
accepted function before it can be emitted or executed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core (Word)
open Solcore.Core.Wire

def wordFunctionVersion : String := "core-word-function-v1"
def abstractionVersion : String := "word-literal-preorder-v1"

/-- Word literals in scalar-expression preorder, including unselected branches. -/
def wordLiterals : Expr → List Word
  | .word value => [value]
  | .letE initializer body | .binary _ initializer body =>
      wordLiterals initializer ++ wordLiterals body
  | .ifE condition yes no | .ternary _ condition yes no =>
      wordLiterals condition ++ wordLiterals yes ++ wordLiterals no
  | .unary _ operand => wordLiterals operand
  | _ => []

def literalCount (body : Expr) : Nat := (wordLiterals body).length

private def abstractAt (depth selected : Nat) : Expr → Option Expr
  | .word _ => if selected = 0 then some (.var depth) else none
  | .letE initializer body =>
      let before := literalCount initializer
      if selected < before then
        (fun changed => .letE changed body) <$> abstractAt depth selected initializer
      else
        .letE initializer <$> abstractAt (depth + 1) (selected - before) body
  | .ifE condition yes no =>
      let before := literalCount condition
      let middle := literalCount yes
      if selected < before then
        (fun changed => .ifE changed yes no) <$> abstractAt depth selected condition
      else if selected < before + middle then
        (fun changed => .ifE condition changed no) <$> abstractAt depth (selected - before) yes
      else
        .ifE condition yes <$> abstractAt depth (selected - before - middle) no
  | .unary operation operand =>
      .unary operation <$> abstractAt depth selected operand
  | .binary operation left right =>
      let before := literalCount left
      if selected < before then
        (fun changed => .binary operation changed right) <$> abstractAt depth selected left
      else
        .binary operation left <$> abstractAt depth (selected - before) right
  | .ternary operation first second third =>
      let before := literalCount first
      let middle := literalCount second
      if selected < before then
        (fun changed => .ternary operation changed second third) <$> abstractAt depth selected first
      else if selected < before + middle then
        (fun changed => .ternary operation first changed third) <$>
          abstractAt depth (selected - before) second
      else
        .ternary operation first second <$> abstractAt depth (selected - before - middle) third
  | _ => none

/-- Replace exactly the selected scalar Word literal by an outer Word input.
Existing locals keep their indices. A `let` increases the replacement index
only in its body, so its initializer still sees the surrounding environment.
An out-of-range selection is explicitly rejected. -/
def abstractWordLiteral (body : Expr) (selected : Nat) : Option Expr :=
  if selected < literalCount body then abstractAt 0 selected body else none

theorem abstractWordLiteral_out_of_range (body : Expr) (selected : Nat)
    (outside : literalCount body ≤ selected) : abstractWordLiteral body selected = none := by
  simp [abstractWordLiteral, Nat.not_lt.mpr outside]

def wordFunctionProgram (body : Expr) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := .lambda .word .word body
}

/-- A single Word parameter is the only free scalar binding allowed in `body`.
The private constructor seals both that scope boundary and full Core typing. -/
structure CheckedWordFunction where private mk ::
  body : Expr
  checked : (wordFunctionProgram body).check = true
  fragment : acceptsAt 1 .word body = true

namespace CheckedWordFunction

def program (function : CheckedWordFunction) : Program := wordFunctionProgram function.body

def ofBody? (body : Expr) : Option CheckedWordFunction :=
  if checked : (wordFunctionProgram body).check = true then
    if fragment : acceptsAt 1 .word body = true then
      some ⟨body, checked, fragment⟩
    else none
  else none

/-- Admission accepts only the exact closed Word-to-Word lambda shape. -/
def ofProgram? : Program → Option CheckedWordFunction
  | { resultType := .function .word .word, dataDefinitions := [],
      body := .lambda .word .word body } => ofBody? body
  | _ => none

/-- Select one literal in an already checked G0 program, then check the new
function. Unsupported source-emitter operations remain explicit later errors. -/
def fromProgram? (source : CheckedWordProgram) (selected : Nat) : Option CheckedWordFunction := do
  ofBody? (← abstractWordLiteral source.program.body selected)

theorem wellTyped (function : CheckedWordFunction) : function.program.WellTyped :=
  Program.check_full_sound function.checked

/-- Apply the original Core lambda to the runtime input. No source or Hull
compilation participates in this independent observation path. -/
def instantiate (function : CheckedWordFunction) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply function.program.body (.word input)
}

theorem instantiate_wellTyped (function : CheckedWordFunction) (input : Word) :
    (function.instantiate input).WellTyped := by
  refine ⟨function.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply function.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (function : CheckedWordFunction) (input : Word) :
    (function.instantiate input).check = true :=
  Program.check_complete (function.instantiate_wellTyped input)

end CheckedWordFunction
end Solcore.Synthesis.Core
