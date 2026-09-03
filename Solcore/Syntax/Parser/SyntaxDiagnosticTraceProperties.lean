import Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties
import Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
import Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties
import Solcore.Syntax.DeclarativeIdentifierCascadeProperties
import Solcore.Syntax.Parser.PublicPragmaSuccessOutputProperties
import Solcore.Syntax.Parser.PublicEmptyTokensOutputProperties
import Solcore.Syntax.Parser.TransactionalChoiceDiagnosticTraceProperties

/-! Exact primitive, successful pragma, and recovery traces with independent
mixed-report filtering. Complete public slices cover empty tokens, one top-item
recovery, one successful pragma, and a missing pragma name. Sequencing and transactional
choice have separate compositional execution laws; general traces remain open. -/
