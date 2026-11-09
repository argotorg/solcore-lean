import Solcore.SourceSemantics.Staging.Stage
import Solcore.SourceSemantics.Staging.Classification
import Solcore.SourceSemantics.Staging.Materialization
import Solcore.SourceSemantics.Staging.Program
import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.Staging.Erasure

import Solcore.SourceSemantics.Staging.Internal.TraceSize

/-!
# Declarative source staging

This umbrella exposes occurrence classification, mutable-local deferral,
whole-program staging admission, compile-time evaluation boundaries, and the
closed materialization relation.  The rules are independent of the executable
stage-analysis pass.

## Reading order

`Stage`, `Classification`, `Program` and `Materialization` state the judgments. `RecursiveProfile`
is the finite staged profile that the source-to-Core theorems are stated over. `Erasure` projects
its traces to the dynamic semantics, and `Preservation` holds its main theorems:
`Staging.Recursive.SelectedPreservation.statements` and
`Staging.Recursive.FaultPreservation.statements`. `Preservation` uses Core lowering files, so this
umbrella does not import it; `Solcore.SourceSemantics.CoreLowering` does.
-/
