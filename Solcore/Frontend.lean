import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.LocalReferenceElaboration
import Solcore.Frontend.LocalReferenceElaborationProperties
import Solcore.Frontend.LocalReferenceEvaluation
import Solcore.Frontend.LocalReferenceExecutionProperties
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalExpressionResolutionProperties
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.LocalExpressionSafetyProperties
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.LocalReferenceEmbeddingProperties
import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalInputsLookupProperties
import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalInputsExecutionProperties

/-!
Canonical local-reference and conditional-expression semantic adapters with
explicit caller-supplied name, type, and runtime tables. Independent source
typing and evaluation correspond exactly to checked Core execution. No source
program resolution, parser change, or wire publication is implied.
-/
