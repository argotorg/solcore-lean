import Solcore.Syntax.DeclarativePragmaSequenceTraceGrammar
import Solcore.Syntax.DeclarativePragmaRejectionTraceGrammar

/-! Independent successful pragma prefixes ending at a recognized rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Written successful declarations precede a recognized rejected pragma.
The endpoint is that last declaration's start, not its internal failure point.
The trace contains prior events only; the separate final report is committed
once by the enclosing file boundary. -/
inductive PragmaPrefixBoundaryTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.PragmaDecl → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop where
  | stopped {input afterKeyword rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (marker : SourceSpan)
      (recognized : ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword)
      (rejected : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
      PragmaPrefixBoundaryTraceParses source endByte input [] input diagnostic trace
  | cons {input afterHead stopped : Remainder}
      {head : Syntax.PragmaDecl} {tail : List Syntax.PragmaDecl}
      {diagnostic : ParseDiagnostic} {headTrace tailTrace : List ParseDiagnostic}
      (headParsed : PragmaDeclTraceParses input head afterHead headTrace)
      (tailParsed : PragmaPrefixBoundaryTraceParses source endByte
        afterHead tail stopped diagnostic tailTrace) :
      PragmaPrefixBoundaryTraceParses source endByte input (head :: tail)
        stopped diagnostic (headTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
