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

theorem Code.emitted
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    code.lowered.expression = Core.LanguageResult.success (code.descriptor.wrap
      (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
        (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody))) := by
  have raw := congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.raw.emitted
  have accepted := code.artifact.decoration
  rw [raw] at accepted
  have expected := code.decoration (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
    (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody))
  have same := Except.ok.inj (accepted.symm.trans expected)
  exact (congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.emitted).trans same

theorem Code.rawBody_hasType
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    Core.HasType (code.artifact.raw.parameterCore :: SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      code.artifact.raw.rawBody (Core.LanguageResult.resultType code.artifact.raw.resultCore) catalog.definitions := by
  have typed := code.outputTyped
  rw [code.emitted] at typed
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

/-- The actual emitted wrapper preserves the renamed code and the real capture
layout while retaining the exact artifact descriptor. -/
theorem formation {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (store : Core.Store) :
    Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
      (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        layout.embedding actual code.descriptor.id)) store ∧
    Represents catalog program bodyCertificate table mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        layout.embedding actual code.descriptor.id)
      (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) := by
  refine ⟨?_, .closure layout code⟩
  rw [code.emitted]
  exact .inRight (.pair (.pair (.inLeft .unit) .lambda) .word)

/-- Ordinary source lambda formation corresponds to the authenticated wrapper.
This does not add the separate runtime stage-call guard to source evaluation. -/
theorem formation_corresponds {actual : Core.Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (heap : Dynamic.Heap) (store : Core.Store) (requirements : code.node.requirements = [])
    (coercions : code.node.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured
      heap code.id (.closure function) heap ∧
    Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
      (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        layout.embedding actual code.descriptor.id)) store ∧
    Represents catalog program bodyCertificate table mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        layout.embedding actual code.descriptor.id)
      (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) := by
  refine ⟨?_, formation layout code store⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.artifact.raw.found)
  · rw [code.artifact.raw.form, requirements, coercions]
    exact .lambda rfl
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
