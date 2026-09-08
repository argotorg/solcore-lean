import Solcore.Resolved.Identity
import Solcore.Resolved.LocalScope
import Solcore.Resolved.LocalScopeProperties
import Solcore.Resolved.Expr
import Solcore.Resolved.LoweringProperties
import Solcore.Resolved.Typing
import Solcore.Resolved.TypingProperties
import Solcore.Resolved.Eval
import Solcore.Resolved.EvaluationProperties
import Solcore.Resolved.ExecutionProperties
import Solcore.Resolved.Scope
import Solcore.Resolved.ScopeProperties
import Solcore.Resolved.Renaming
import Solcore.Resolved.RenamingProperties

/-!
Semantic frontend foundation for already-resolved local expressions. Exact
lookup, elaboration, typing, evaluation, and executable Core correspondence;
not a canonical source resolver or a complete source-to-Core pipeline.
-/
