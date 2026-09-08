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
import Solcore.Resolved.FreshIdentity
import Solcore.Resolved.ScopeExtensionProperties
import Solcore.Resolved.ScopeExtensionEvaluationProperties
import Solcore.Resolved.ScopeExtensionReflectionProperties
import Solcore.Resolved.WordLessWithIds
import Solcore.Resolved.WordLessWithIdsEvaluationProperties
import Solcore.Resolved.LocalFragmentProperties

/-!
Semantic frontend foundation for already-resolved local expressions. Exact
lookup, elaboration, typing, evaluation, and executable Core correspondence;
ordered binary products retain the original child scopes and actual values.
This is not a canonical source resolver or a complete source-to-Core pipeline,
and does not itself enable a canonical tuple adapter.
-/
