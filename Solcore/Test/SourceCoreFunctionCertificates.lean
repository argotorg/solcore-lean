import Solcore.SourceSemantics.CoreLowering.FunctionValues

/-! Actual lambda lowering, independent source formation, and a cyclic
capture through a mapped cell after administrative layout insertion.  The
body compiler is the existing basic compiler restricted to an empty Unit
body; no body execution appears in the code-authentication premise. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap FunctionCode FunctionCaptures

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"function_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def self : Resolved.LocalId := ⟨owner, 0⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "function_certificates.solc"⟩, 0, 1⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def program : Program := ⟨signatures, [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.TaggedFunction.functionType .unit .unit
private def cellType : Core.Ty := Core.OptionalCell.cellType functionType
private def scope : SourceCoreLocalCell.Scope := [(self, functionType)]
private def node : ExpressionNode := { id, span, type := sourceType, form := .lambda [] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression node] }
private def context : SourceSemantics.Context := {
  (SourceSemantics.Context.ofSignatures signatures).withLocal self (.mono sourceType) [] with
  currentDeclaration := some owner, residualTypeVariables := true }
private def function : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [], source
  captured := [(self, ⟨0⟩)], context, evidence := [] }
private def compilation : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0
  solvedRequirements := [], internalReason := Core.Word.zero }
private def policy : SourceCoreFunctions.Policy := {}
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun _ budget source scope statements result _ reason _ =>
    SourceCoreBasic.lowerStatements budget source scope statements result reason
private def bodyCertificate : BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = Core.LanguageResult.success .unit
private def emitted : SourceCoreBasic.LoweredExpr := ⟨functionType,
  Core.LanguageResult.success (Core.TaggedFunction.anonymous
    (.lambda .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit)))⟩

private theorem artifact_exists : Nonempty
    (LambdaCertificate bodyCertificate policy source scope id node [] .unit [] functionType emitted) := by
  apply lambda_of_accepted (lowerBody := lowerBody) (fuel := 1) (context := compilation)
    (reasonAt := fun _ => Core.Word.zero) rfl rfl rfl rfl
  · intro budget bodyScope type code accepted
    simp only [lowerBody, SourceCoreBasic.lowerStatements] at accepted
    split at accepted
    · next same => cases accepted; exact ⟨rfl, same, rfl⟩
    · cases accepted
  · cbv

private noncomputable def artifact : LambdaCertificate bodyCertificate policy source scope id node [] .unit [] functionType emitted :=
  Classical.choice artifact_exists

private theorem parameter_type : artifact.parameterCore = .unit := by
  have selected := artifact.parameterProjection
  rw [← artifact.bundle] at selected
  exact Except.ok.inj selected.symm

private theorem result_type : artifact.resultCore = .unit := Except.ok.inj artifact.resultProjection.symm

private theorem graph : OccurrenceGraphWellFormed source := by
  constructor
  · unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  · intro selected member
    simp only [source, List.mem_singleton] at member
    subst selected
    rfl
  · intro root member
    simp only [source, List.mem_singleton] at member
    subst root
    rfl
  · intro root member
    simpa [source, nodeIds, Node.id, node] using member
  · intro selected member child childMember
    simp only [source, List.mem_singleton] at member
    subst selected
    cases childMember

private theorem frame : Dynamic.ClosureFrame program function := by
  have unique : RequirementIdsUnique context := by
    simp [RequirementIdsUnique, context, Context.withLocal, Context.ofSignatures]
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence impossible
      cases impossible
    · intro predicate impossible
      cases impossible
  refine ⟨rfl, rfl, ?_, unique, covers⟩
  refine ⟨rfl, rfl, rfl, rfl, graph, ⟨unique, ?_⟩, ?_⟩
  · intro row evidence member
    cases member
  · refine ⟨id, node, ⟨by change Node.expression node ∈ [Node.expression node]; exact List.mem_singleton_self _, rfl⟩, rfl, rfl, ?_⟩
    exact .lambda (by decide) (.nil _) (.nil _ _) ⟨rfl, rfl, .inr rfl⟩

private def world : Core.StoreTyping := [.word, .unit, cellType]
private def canonical : Core.Environment := [.cellRef cellType 2, .bool false]
private def actual : Core.Environment := [.integer 11, .cellRef cellType 2, .bool false]
private def sourceHeap : Dynamic.Heap := ⟨[⟨sourceType, none, none⟩]⟩
private def store : Core.Store := [.word Core.Word.zero, .unit, .inLeft functionType .unit]
private def layout : Layout catalog [2] world scope function.captured actual where
  administrativeContext := [.bool]
  canonical := canonical
  actualContext := [.integer, .cell cellType, .bool]
  embedding := Core.Renaming.insertion 0
  represented := .cons ⟨rfl, rfl⟩ (.nil (.cons .bool .nil))
  lookups := Core.ReadOnly.EnvironmentsAgree.insertion canonical 0 (.integer 11)
  types := Core.Renaming.insertion_respects_insertAt [.cell cellType, .bool] 0 .integer
  actualTyped := .cons .integer (.cons (.cellRef rfl) (.cons .bool .nil))

private def captures : Certificate catalog [2] world sourceHeap context scope function.captured actual :=
  ⟨layout, .cons (.intro .head) rfl (.ordinary rfl rfl) .nil⟩

private noncomputable def code : FunctionValues.Code catalog program bodyCertificate policy function scope [.bool] where
  id := id
  node := node
  reportedType := functionType
  lowered := emitted
  artifact := artifact
  frame := frame
  projection := by
    rw [parameter_type, result_type]
    rfl
  outputTyped := by
    rw [parameter_type, result_type]
    exact .inRight .word (.pair (.inLeft .word .unit) (.lambda .unit (.sum .word .unit) (.inRight .word .unit)))

/-- The source cell can be uninitialized when the closure captures it. -/
example : FunctionValues.SourceCapturesValid sourceHeap (.closure function) := captures.sourceMetadata

/-- The actual lowering certificate gives independent source formation and a
Core closure whose capture includes the inserted Integer slot. -/
example : Dynamic.ExpressionEvaluates program context [] source function.captured sourceHeap id (.closure function) sourceHeap ∧
    Core.Evaluates actual store (emitted.expression.rename layout.embedding)
      (.inRight .word (FunctionValues.value code.artifact.parameterCore code.artifact.resultCore
        code.artifact.rawBody layout.embedding actual)) store := by
  exact ⟨(FunctionValues.formation_corresponds layout code sourceHeap store rfl rfl).1,
    (FunctionValues.formation_corresponds layout code sourceHeap store rfl rfl).2.1⟩

private def model : GenericHeap.PayloadModel catalog := FunctionValues.model catalog program bodyCertificate policy
private noncomputable def generated : Core.Value :=
  FunctionValues.value artifact.parameterCore artifact.resultCore artifact.rawBody layout.embedding actual
private theorem represented : model.Represents [2] world sourceType (.closure function) generated functionType := by
  have related := FunctionValues.Represents.closure layout code
  change FunctionValues.Represents catalog program bodyCertificate policy [2] world sourceType
    (.closure function) generated (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore) at related
  rw [parameter_type, result_type] at related
  exact related

private theorem initialHeap : GenericHeap.HeapRepresents model [2] world sourceHeap store := by
  have empty := GenericHeap.HeapRepresents.empty (model := model)
  have administrative := (empty.allocate_administrative (.word (value := Core.Word.zero))).allocate_administrative .unit
  exact (administrative.allocate (.uninitialized rfl) .append).1

private def installedHeap : Dynamic.Heap := ⟨[⟨sourceType, some (.closure function), none⟩]⟩
private noncomputable def installedStore : Core.Store := [.word Core.Word.zero, .unit, .inRight .unit generated]

/-- The generated closure can be installed in the cell it captures. The
source and Core indices differ, and no recursive heap-unfolding proof is used. -/
private theorem installed : GenericHeap.HeapRepresents model [2] world installedHeap installedStore := by
  obtain ⟨updated, written, related, _⟩ := initialHeap.write_initialized
    (reference := ⟨rfl, rfl⟩) (.intro .head) represented (.intro (.intro .head) .head)
  have exactWrite : store.write? 2 (.inRight .unit generated) = some installedStore := rfl
  have same := Option.some.inj (written.symm.trans exactWrite)
  exact same ▸ related

example : Core.RuntimeStoreHasTypes world installedStore catalog.definitions := installed.runtime_hasTypes

example : GenericHeap.HeapRepresents model [2] (world ++ [.integer]) installedHeap
    (installedStore ++ [.integer 81]) := installed.allocate_administrative .integer

example : Dynamic.ValueHasType context installedHeap (.closure function) sourceType :=
  FunctionValues.Represents.source_hasType represented rfl
    (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)

example (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities functionType (.closure function) generated :=
  FunctionValues.Represents.observation represented signatures identities

end Tests.SourceCoreFunctionCertificates
