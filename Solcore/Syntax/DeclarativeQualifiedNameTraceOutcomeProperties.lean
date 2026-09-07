import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Unconditional joint exactness for maximal checked qualified names and
their dotted tails. These bundles assert uniqueness/disjointness, not existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem dottedIdentifierTailTraceExactOutcomeSpec (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec DottedIdentifierTailTraceParses
      (DottedIdentifierTailTraceRejects context) source endByte where
  successResultUnique := DottedIdentifierTailTraceParses.result_unique
  rejectResultUnique := DottedIdentifierTailTraceRejects.result_unique
  successRejectDisjoint := DottedIdentifierTailTraceRejects.disjoint_success

theorem qualifiedNameTraceExactOutcomeSpec (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec QualifiedNameTraceParses
      (QualifiedNameTraceRejects context) source endByte where
  successResultUnique := QualifiedNameTraceParses.result_unique
  rejectResultUnique := QualifiedNameTraceRejects.result_unique
  successRejectDisjoint := QualifiedNameTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
