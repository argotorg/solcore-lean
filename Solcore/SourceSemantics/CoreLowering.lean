import Solcore.SourceSemantics.CoreLowering.StagedValue
import Solcore.SourceSemantics.CoreLowering.Literals
import Solcore.SourceSemantics.CoreLowering.LocalCell
import Solcore.SourceSemantics.CoreLowering.HeapMutation
import Solcore.SourceSemantics.CoreLowering.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.BasicStatements

/-! Proofs connecting executable Core lowering to the independent source
semantics. This boundary is separate from the specification's umbrella so that
the specification does not depend on executable frontend passes. -/
