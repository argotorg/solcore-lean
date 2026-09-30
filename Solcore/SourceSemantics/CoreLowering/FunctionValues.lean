import Solcore.SourceSemantics.CoreLowering.FunctionCodeCertificates
import Solcore.SourceSemantics.CoreLowering.FunctionCaptures
import Solcore.SourceSemantics.CoreLowering.DataEqualityValues

/-! Authenticated ordinary lambda leaves for the generic payload model.

The source frame and actual compiler structure are static certificates.  Core
typing authenticates the emitted wrapper in its canonical lexical context.
The value relation retains the real renamed code and captured environment;
it never identifies closures made under different administrative layouts.

Exact source capture metadata is heap indexed and supplied separately.  None
of these certificates assumes a child execution or proves function-call
meaning. Named functions, builtin values, generalized local closures, and
stage guards remain separate obligations.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionValues

open Frontend Frontend.SourceInference GeneralHeap FunctionCode

def sourceType (function : Dynamic.Closure) : TypeSystem.Ty :=
  .function (TypeSystem.Ty.productMany (function.parameters.map (·.scheme.body))) function.resultType

structure Code (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (function : Dynamic.Closure) (scope : SourceCoreLocalCell.Scope)
    (administrativeContext : Core.Context) where
  id : ExpressionId
  node : ExpressionNode
  reportedType : Core.Ty
  lowered : SourceCoreBasic.LoweredExpr
  artifact : LambdaCertificate bodyCertificate policy function.source scope id node
    function.parameters function.resultType function.body reportedType lowered
  frame : Dynamic.ClosureFrame program function
  projection : catalog.project (sourceType function) = .ok
    (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore)
  outputTyped : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
    lowered.expression (Core.LanguageResult.resultType
      (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore)) catalog.definitions

def value (parameter result : Core.Ty) (body : Core.Expr)
    (embedding : Core.Renaming) (captured : Core.Environment) : Core.Value :=
  .pair (.inLeft .word .unit)
    (.closure parameter (Core.LanguageResult.resultType result) (body.rename embedding.lift) captured)

/-- Only ordinary anonymous source lambdas inhabit this leaf model.  Other
function identities can be composed with it through a separate constructor. -/
inductive Represents (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
      (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext) :
      Represents catalog program bodyCertificate policy mapping world (sourceType function) (.closure function)
        (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual)
        (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore)

variable {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
  {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
  {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
  {type : TypeSystem.Ty} {source : Dynamic.Value} {core : Core.Value} {payload : Core.Ty}

theorem Represents.projection
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload) :
    catalog.project type = .ok payload := by
  cases related with
  | closure _ code => exact code.projection

theorem Represents.runtime_hasType
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload) :
    Core.RuntimeValueHasType world core payload catalog.definitions := by
  cases related with
  | closure layout code =>
    exact .pair (.inLeft .unit) (.closure layout.actualTyped
      (code.artifact.rawBody_hasType code.outputTyped |>.rename (layout.types.lift _)))

theorem Represents.observation
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    (signatures : ProgramSignatures) (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities payload source core := by
  cases related with
  | closure layout code => exact .anonymous _ _ _ _

theorem Represents.extend
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    Represents catalog program bodyCertificate policy futureMapping futureWorld type source core payload := by
  cases related with
  | closure layout code => exact .closure (layout.extend maps worlds) code

def model (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy) : GenericHeap.PayloadModel catalog where
  Represents := Represents catalog program bodyCertificate policy
  projection := Represents.projection
  runtime_hasType := Represents.runtime_hasType
  extend := Represents.extend

/-- Source lexical validity observes source cell declarations and generalized
storage metadata. It cannot be recovered from projected Core types alone. -/
def SourceCapturesValid (heap : Dynamic.Heap) : Dynamic.Value → Prop
  | .closure function => Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  | _ => False

theorem SourceCapturesValid.extend {heap futureHeap : Dynamic.Heap}
    (valid : SourceCapturesValid heap source) (metadata : Dynamic.HeapMetadataExtend heap futureHeap) :
    SourceCapturesValid futureHeap source := by
  cases source <;> try cases valid
  exact valid.mono metadata

/-- The two independent parts together imply declarative source value typing.
This theorem still contains no assumption about executing the closure body. -/
theorem Represents.source_hasType
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    {heap : Dynamic.Heap} {context : Context}
    (signatures : context.signatures = program.signatures)
    (captures : SourceCapturesValid heap source) : Dynamic.ValueHasType context heap source type := by
  cases related with
  | closure layout code =>
    exact .closure (code.frame.signatures.trans signatures.symm) code.frame.code code.frame.evidence_covers captures

/-- Formation evaluates the actual emitted code under the actual environment.
The result records its renamed body and all administrative captures. -/
theorem formation
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (store : Core.Store) :
    Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
      (.inRight .word (value code.artifact.parameterCore code.artifact.resultCore
        code.artifact.rawBody layout.embedding actual)) store ∧
    Represents catalog program bodyCertificate policy mapping world (sourceType function) (.closure function)
      (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual)
      (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore) := by
  refine ⟨?_, .closure layout code⟩
  have emitted := congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.emitted
  rw [emitted]
  exact .inRight (.pair (.inLeft .unit) .lambda)

/-- Independent source formation and the emitted Core lambda describe the
same closure. Output coercions and requirement execution are deliberately
outside this ordinary formation rule. -/
theorem formation_corresponds
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (heap : Dynamic.Heap) (store : Core.Store)
    (requirements : code.node.requirements = []) (coercions : code.node.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured
      heap code.id (.closure function) heap ∧
    Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
      (.inRight .word (value code.artifact.parameterCore code.artifact.resultCore
        code.artifact.rawBody layout.embedding actual)) store ∧
    Represents catalog program bodyCertificate policy mapping world (sourceType function) (.closure function)
      (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual)
      (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore) := by
  refine ⟨?_, formation layout code store⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.artifact.found)
  · rw [code.artifact.form, requirements, coercions]
    exact .lambda rfl
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.FunctionValues
