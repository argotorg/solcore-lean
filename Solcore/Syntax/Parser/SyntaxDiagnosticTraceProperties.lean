import Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties
import Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
import Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties
import Solcore.Syntax.DeclarativeIdentifierCascadeProperties

/-! Exact identifier and recovery traces, primitive rejection reports, complete
single-recovery and missing-pragma-name outputs, and independent mixed-report
cascade filtering. General declaration and nested-isolation traces remain separate. -/
