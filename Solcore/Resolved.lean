import Solcore.Resolved.Identity
import Solcore.Resolved.LocalScope
import Solcore.Resolved.Expr
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.Resolved.ExecutionProperties
import Solcore.Resolved.Internal.ScopeLaws

/-!
# Resolved expressions

The semantic foundation for already-resolved local expressions: exact lookup, elaboration, typing,
evaluation, and correspondence with executable Core. Ordered binary products keep the original child
scopes and actual values. This is not a canonical source resolver or a complete source-to-Core
pipeline, and it does not enable a canonical tuple adapter. `docs/review/foundations.md` lists every
file.

Read `Identity`, `LocalScope`, `Expr`, `Typing` and `Eval`. `ExecutionProperties` holds the main
theorems, and `Internal/ScopeLaws` scope and renaming.
-/
