import Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties
import Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
import Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties

/-! Exact diagnostic traces for standalone top-item recovery, a single
unrecognized recovery-to-end file, and a missing-name pragma boundary stop,
including independent primitive rejection reports and lexical-cascade
filtering and complete public output equality. -/
