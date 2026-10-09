import Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning

/-! The flow path is produced at the original lexical joins. A body packet
retains that same flow fault and native body completion at the body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open NamedLexicalFlowFaultPostContracts NamedLexicalFunctionFaultPostContracts

abbrev BodyPath (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (reason : Dynamic.SemanticFault)
    (after : Dynamic.Heap) (token : Word) (mapping : LocationMap) (world : StoreTyping) (store : Store) :=
  FlowOrigin post program function.evidence function.source context environment before true function.body
    reason after token mapping world store

/-- Lexical finish retains the original child post, including callable
children, at the same actual body store. -/
def bodyPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) :
    NamedInvocationFaultPostContracts.BodyFaultPost :=
  fun program function context environment before actual initialStore body reason after token mapping world bodyStore =>
    ∃ sourceSize finalContext type,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext (.fault reason) after ∧
      BodyPath post
        program function context environment before reason after token mapping world bodyStore ∧
      Evaluates actual initialStore body (.inLeft type (.word token)) bodyStore

def model_bodyPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    NamedInvocationFaultPostContracts.BodyFaultPost :=
  bodyPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry)

/-- The lexical exit and original finish evaluation preserve the same child
fault origin. No second flow or finish evaluation is constructed. -/
theorem outcome_post_of_finished_for
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {expressionSyntax : ExpressionId → Prop} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : LocationMap} {world : StoreTyping} {bodyStore initialStore : Store} {actual : Environment} {body : Expr}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax context true function.body function.resultType)
    (unique : NodeOccurrencesUnique function.source)
    (retained : FinishedPost (FlowPost post)
      program function context environment before size type outcome after value mapping world bodyStore)
    (evaluated : Evaluates actual initialStore body value bodyStore) :
    NamedInvocationFaultPostContracts.OutcomePost (bodyPost post) program function context
      environment before actual initialStore body type outcome after value mapping world bodyStore := by
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨finalContext, control, trace, exit, origin⟩ := retained
    cases exit with
    | fault =>
      obtain ⟨token, same, path⟩ := origin
      exact ⟨token, same, size, finalContext, type, trace, path, same ▸ evaluated⟩
    | breaking next =>
      cases trace with
      | control executed => cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed.sound
    | continuing next =>
      cases trace with
      | control executed => cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed.sound

/-- The retained actual flow and exit select the same fault. Successful lexical
syntax excludes direct transfers; it supplies no primitive fault origin. -/
theorem outcome_post_of_finished {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {expressionSyntax : ExpressionId → Prop} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : LocationMap} {world : StoreTyping} {bodyStore initialStore : Store} {actual : Environment} {body : Expr}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax context true function.body function.resultType)
    (unique : NodeOccurrencesUnique function.source)
    (retained : FinishedPost (FlowPost (ReachedBuiltinExpressionFaultPaths.model_expressionPost checked functions registry))
      program function context environment before size type outcome after value mapping world bodyStore)
    (evaluated : Evaluates actual initialStore body value bodyStore) :
    NamedInvocationFaultPostContracts.OutcomePost (model_bodyPost checked functions registry) program function context
      environment before actual initialStore body type outcome after value mapping world bodyStore := by
  exact outcome_post_of_finished_for syntaxTree unique retained evaluated

end Solcore.SourceSemantics.CoreLowering.ReachedNamedLexicalBodyFaultPaths
