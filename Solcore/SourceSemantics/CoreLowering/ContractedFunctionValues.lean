import Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
import Solcore.SourceSemantics.CoreLowering.FunctionValues
import Solcore.Frontend.SourceCoreCallableContracts

/-! Anonymous closures with authenticated artifact-owned callable descriptors.
The raw code/captures and the descriptor origin are independent static fields.
The descriptor authenticates its origin lookup; reconstruction of the original
staging flags from prepared source needs the enclosing compiler receipt.
A concrete profile must prove its lambda-decoration equation; code acceptance
alone does not establish that an arbitrary callable hook preserves meaning.

This relation proves formation, typing and world extension. It does not identify
legacy staging guards with the independent source call rules, and does not
import arbitrary external closure bodies or instantiate a full body theorem. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
open Frontend Frontend.SourceInference GeneralHeap

structure Code (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (compilation : SourceCoreFunctions.Context) (table : SourceCoreStageCodebook.Table)
    (active : TypeSystem.Substitution) (function : Dynamic.Closure)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) where
  id : ExpressionId
  node : ExpressionNode
  reportedType : Core.Ty
  lowered : SourceCoreBasic.LoweredExpr
  artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation function.source scope id node
    function.parameters function.resultType function.body reportedType lowered
  owner : compilation.owner.declaration = function.source.owner
  descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active)
  decoration : ∀ value, policy.callables.decorateCallable compilation function.source node (.lambda id)
    artifact.raw.parameterCore artifact.raw.resultCore (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value))
  frame : Dynamic.ClosureFrame program function
  projection : catalog.project (FunctionValues.sourceType function) = .ok
    (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)
  outputTyped : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
    lowered.expression (Core.LanguageResult.resultType
      (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)) catalog.definitions

variable {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
  {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
  {compilation : SourceCoreFunctions.Context} {table : SourceCoreStageCodebook.Table}
  {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrativeContext : Core.Context}

/-- The decorated callable created at the lambda, before its creation-time copies. -/
def Code.callable
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    Core.Expr :=
  Core.LanguageResult.success (code.descriptor.wrap
    (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
      (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody)))

theorem Code.emitted
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    code.lowered.expression =
      SourceCoreSourceCells.copyScopePlain function.source scope (fun index => index) code.callable := by
  have accepted := code.artifact.decoration
  have expected := code.decoration (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
    (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody))
  have same := Except.ok.inj (accepted.symm.trans expected)
  rw [congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.emitted]
  dsimp only
  rw [same]
  rfl

/-- Code validity does not depend on the captured environment, so the same
code describes the closure over any copy of its captures. -/
def Code.recapture
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext)
    (captured : Dynamic.Environment) :
    Code catalog program bodyCertificate policy compilation table active { function with captured := captured }
      scope administrativeContext where
  id := code.id
  node := code.node
  reportedType := code.reportedType
  lowered := code.lowered
  artifact := code.artifact
  owner := code.owner
  descriptor := code.descriptor
  decoration := code.decoration
  frame := ⟨code.frame.signatures, code.frame.owner,
    ⟨code.frame.code.owner, code.frame.code.closed, code.frame.code.variables_closed,
      code.frame.code.residual_variables_open, code.frame.code.graph, code.frame.code.requirement_ledger,
      code.frame.code.occurrence⟩,
    code.frame.requirements, code.frame.evidence_covers⟩
  projection := code.projection
  outputTyped := code.outputTyped

theorem Code.rawBody_hasType
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    Core.HasType (code.artifact.raw.parameterCore :: SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      code.artifact.raw.rawBody (Core.LanguageResult.resultType code.artifact.raw.resultCore) catalog.definitions := by
  have typed := code.outputTyped
  rw [code.emitted] at typed
  replace typed := CaptureCopyTyping.copyScopePlain_body_hasType (fun _ _ same => same) typed
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged _ =>
      cases tagged with
      | pair _ closure =>
        cases closure with
        | lambda _ _ body => exact body

private theorem contracted_catalog {sourceParameter sourceResult : TypeSystem.Ty} {parameter result : Core.Ty}
    (projected : catalog.project (.function sourceParameter sourceResult) =
      .ok (Core.CallableContract.functionType parameter result)) : catalog.callableContracts = true := by
  cases first : catalog.project sourceParameter with
  | error error => simp [SourceCoreDataCatalog.Catalog.project, first, bind, Except.bind] at projected
  | ok parameterType =>
    cases second : catalog.project sourceResult with
    | error error => simp [SourceCoreDataCatalog.Catalog.project, first, second, bind, Except.bind] at projected
    | ok resultType =>
      cases profile : catalog.callableContracts with
      | true => rfl
      | false =>
        simp [SourceCoreDataCatalog.Catalog.project, first, second, SourceCoreDataCatalog.Catalog.functionType,
          profile, Core.TaggedFunction.functionType, Core.CallableContract.functionType,
          Core.TaggedFunction.identityType, bind, Except.bind] at projected

def value (parameter result : Core.Ty) (body : Core.Expr) (embedding : Core.Renaming)
    (captured : Core.Environment) (contract : Core.Word) : Core.Value :=
  .pair (FunctionValues.value parameter result body embedding captured) (.word contract)

inductive Represents (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table)
    (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
      {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
      (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext) :
      Represents catalog program bodyCertificate table mapping world
        (FunctionValues.sourceType function) (.closure function)
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          layout.embedding actual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore)

variable {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
  {type : TypeSystem.Ty} {source : Dynamic.Value} {core : Core.Value} {payload : Core.Ty}

theorem Represents.projection
    (related : Represents catalog program bodyCertificate table mapping world type source core payload) :
    catalog.project type = .ok payload := by
  cases related with
  | closure _ code => exact code.projection

theorem Represents.runtime_hasType
    (related : Represents catalog program bodyCertificate table mapping world type source core payload) :
    Core.RuntimeValueHasType world core payload catalog.definitions := by
  cases related with
  | closure layout code =>
    exact .pair (.pair (.inLeft .unit) (.closure layout.actualTyped
      (code.rawBody_hasType.rename (layout.types.lift _)))) .word

theorem Represents.observation
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    (signatures : ProgramSignatures) (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities payload source core := by
  cases related with
  | closure layout code => exact .contractedAnonymous _ _ _ _ _ (contracted_catalog code.projection)

theorem Represents.extend
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    Represents catalog program bodyCertificate table futureMapping futureWorld type source core payload := by
  cases related with
  | closure layout code => exact .closure (layout.extend maps worlds) code

def model (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table) :
    GenericHeap.PayloadModel catalog where
  Represents := Represents catalog program bodyCertificate table
  projection := Represents.projection
  runtime_hasType := Represents.runtime_hasType
  extend := Represents.extend

theorem Represents.source_hasType
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    {heap : Dynamic.Heap} {context : Context} (signatures : context.signatures = program.signatures)
    (captures : FunctionValues.SourceCapturesValid heap source) : Dynamic.ValueHasType context heap source type := by
  cases related with
  | closure layout code =>
    exact .closure (code.frame.signatures.trans signatures.symm) code.frame.code code.frame.evidence_covers captures

/-- The actual emitted wrapper copies the captured cells of its creation
environment, then preserves the renamed code and the closure's capture layout
while retaining the exact artifact descriptor. -/
theorem formation {model : GenericHeap.PayloadModel catalog}
    {environment : Dynamic.Environment} {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.EnvironmentCopies function.source environment heap captured finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)) finalStore ∧
      Represents catalog program bodyCertificate table finalMap finalWorld
        (FunctionValues.sourceType function) (.closure { function with captured := captured })
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap,
      finalWorld, finalEmbedding, copy, environments, finalHeaps, maps, worlds, frame, lookups, types,
      actualTyped, agreement⟩ :=
    CaptureCopies.copies_prefix_typed (pre := []) (preContext := [])
      (body := code.callable) layout.represented heaps
      layout.lookups rfl layout.types layout.actualTyped
  let closureLayout : FunctionCaptures.Layout catalog finalMap finalWorld scope captured finalActual := {
    administrativeContext := layout.administrativeContext
    canonical := finalCanonical
    actualContext := finalActualContext
    embedding := finalEmbedding
    represented := environments
    lookups := lookups
    types := types
    actualTyped := actualTyped }
  have represented : Represents catalog program bodyCertificate table finalMap finalWorld
      (FunctionValues.sourceType { function with captured := captured }) (.closure { function with captured := captured })
      (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        finalEmbedding finalActual code.descriptor.id)
      (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) := by
    exact @Represents.closure catalog program bodyCertificate table finalMap finalWorld policy compilation active
      { function with captured := captured } scope finalActual closureLayout (code.recapture captured)
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, finalActual, finalEmbedding, copy, ?_,
    represented, finalHeaps, maps, worlds, frame⟩
  rw [code.emitted]
  have base : (fun index : Nat => index) = (· + ([] : Core.Environment).length) := by
    funext index
    simp
  rw [base]
  apply agreement.wrap
  exact .inRight (.pair (.pair (.inLeft .unit) .lambda) .word)

/-- Ordinary source lambda formation over copies of its creation environment
corresponds to the authenticated wrapper. This does not add the separate
runtime stage-call guard to source evaluation. -/
theorem formation_corresponds {model : GenericHeap.PayloadModel catalog}
    {environment : Dynamic.Environment} {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (requirements : code.node.requirements = []) (coercions : code.node.coercions = []) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment
        heap code.id (.closure { function with captured := captured }) finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)) finalStore ∧
      Represents catalog program bodyCertificate table finalMap finalWorld
        (FunctionValues.sourceType function) (.closure { function with captured := captured })
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, copy, evaluated,
      represented, heaps, maps, worlds, frame⟩ := formation layout code heaps
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, ?_, evaluated,
    represented, heaps, maps, worlds, frame⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.artifact.raw.found)
  · rw [code.artifact.raw.form, requirements, coercions]
    exact .lambda rfl copy
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
