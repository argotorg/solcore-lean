import Solcore.Syntax.DeclarativePragmaTraceGrammar

/-! Independent exact syntax and raw diagnostic traces for complete windows
containing only successful pragmas. No executor state, reply, or fuel occurs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The source-order top-level node belonging to one exact pragma declaration. -/
def pragmaSequenceItem (declaration : Syntax.PragmaDecl) : Syntax.TopItem := {
  span := declaration.span, leadingComments := [], value := .pragmaDecl declaration
}

/-- Lift written declarations without changing their order or multiplicity. -/
def pragmaSequenceItems (declarations : List Syntax.PragmaDecl) : List Syntax.TopItem :=
  declarations.map pragmaSequenceItem

/-- Exact pragma-only scan through the active window end. Each declaration
contributes its checked-item events, followed by the suffix's events. -/
inductive PragmaSequenceTraceParses :
    Remainder → List Syntax.PragmaDecl → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      PragmaSequenceTraceParses input [] input []
  | cons {input afterHead output : Remainder}
      {head : Syntax.PragmaDecl} {tail : List Syntax.PragmaDecl}
      {headTrace tailTrace : List ParseDiagnostic}
      (headParsed : PragmaDeclTraceParses input head afterHead headTrace)
      (tailParsed : PragmaSequenceTraceParses afterHead tail output tailTrace) :
      PragmaSequenceTraceParses input (head :: tail) output (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
