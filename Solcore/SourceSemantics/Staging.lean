import Solcore.SourceSemantics.Staging.Stage
import Solcore.SourceSemantics.Staging.Assignment
import Solcore.SourceSemantics.Staging.Classification
import Solcore.SourceSemantics.Staging.Materialization
import Solcore.SourceSemantics.Staging.Program
import Solcore.SourceSemantics.Staging.RecursiveScope
import Solcore.SourceSemantics.Staging.RecursiveTrace
import Solcore.SourceSemantics.Staging.RecursiveTraceProperties

/-!
# Declarative source staging

This umbrella exposes occurrence classification, mutable-local deferral,
whole-program staging admission, compile-time evaluation boundaries, and the
closed materialization relation.  The rules are independent of the executable
stage-analysis pass.
-/
