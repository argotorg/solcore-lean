import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Index
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Recursive formation tests

Formation of recursive closures from named results through public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationCollection
/-! Extract selected functions from an authentic named result. The whole Source
value and native payload come from execution; the real recursive export supplies
ordered leaves and each leaf's validation budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Entry Caller Result Addition)
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  {artifact : Artifact} {checkpoint : Checkpoint artifact} {completion : Completion artifact}
  {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}

/-- The genuine full result and successful output receipt determine the selected
Source leaves and the exact history addition, with no body or encoding premise. -/
theorem named_collection {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : completion.session.RegistryAt actualRegistry)
    (extension : SourceCoreRawMetadata.Extends receiving actualRegistry)
    (selection : Selection header.function.resultType completion.value) :
    ∃ (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      Selected compiled.compatible.checked completion.session selection source payload header.output outputFuel added ∧
      added.map Entry.handle = selection.handles ∧
      Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel
        header.function.resultType header.output outcome native added := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  have nativeValue : native = .inRight .word payload := by
    have represented := result.2.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  have before := atRegistry.symm ▸ extension
  obtain ⟨added, selected, handles⟩ := selection.collect atRecipe
    (congrArg (fun compiled => compiled.compatible.checked) sameCompiled).symm represented
    encodedAt rfl payloadAt before
  exact ⟨source, payload, added, sourceValue, nativeValue, selected, handles,
    .selectNestedCompatible requested rfl sourceValue nativeValue selection selected⟩

/-- Selecting both public function leaves recovers exactly two ordered Source
entries, retaining their original payload types and recursive encoder fuel. -/
theorem pair_entries {checked : SourceCoreCompatibleCatalog.Checked}
    {session : Session artifact} {leftType rightType : TypeSystem.Ty}
    {left right : SourceCorePublicValues.Handle} {source : Dynamic.Value}
    {payload : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session
      (Selection.product (Selection.function (type := leftType) (handle := left))
        (Selection.function (type := rightType) (handle := right)))
      source payload nativeType fuel entries) :
    ∃ first second : Entry,
      entries = [first, second] ∧ source = .product first.source second.source ∧
      first.sourceType = leftType ∧ second.sourceType = rightType ∧
      first.handle = left ∧ second.handle = right := by
  cases selected with
  | product first second =>
      cases first with
      | function firstImported =>
          cases second with
          | function secondImported => exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

def pairSelection {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    {leftType rightType : TypeSystem.Ty} {left right : SourceCorePublicValues.Handle}
    (raw : sourceType = .product leftType rightType)
    (value : publicValue = .product (.function left) (.function right)) : Selection sourceType publicValue := by
  cases raw
  cases value
  exact .product .function .function

/-- Transport along the actual result signature and public value leaves the
selected order and Source product unchanged. -/
theorem pair_selection_entries {checked : SourceCoreCompatibleCatalog.Checked}
    {session : Session artifact} {sourceType leftType rightType : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {left right : SourceCorePublicValues.Handle}
    {source : Dynamic.Value} {payload : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (raw : sourceType = .product leftType rightType)
    (value : publicValue = .product (.function left) (.function right))
    (selected : Selected checked session (pairSelection raw value) source payload nativeType fuel entries) :
    ∃ first second : Entry,
      entries = [first, second] ∧ source = .product first.source second.source ∧
      first.sourceType = leftType ∧ second.sourceType = rightType ∧
      first.handle = left ∧ second.handle = right := by
  cases raw
  cases value
  exact pair_entries selected

theorem encoded_function_shape {session : Session artifact} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {parameter result : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry (.function parameter result) publicValue encoded)
    (paired : ∃ a b, encoded.value = .pair a b) :
    ∃ handle, publicValue = .function handle := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case function handle => exact ⟨handle, rfl⟩
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        obtain ⟨_, _, paired⟩ := paired
        rw [same] at paired
        cases paired

theorem encoded_pair_shape {session : Session artifact} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {leftType rightType : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry (.product leftType rightType) publicValue encoded)
    (paired : ∃ a b, encoded.value = .pair a b) :
    ∃ left right, publicValue = .product left right := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case product left right => exact ⟨left, right, rfl⟩
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        obtain ⟨_, _, paired⟩ := paired
        rw [same] at paired
        cases paired

private theorem native_function_pair {catalog : SourceCoreCompatibleCatalog.Catalog}
    {native : Core.Value} {parameter result : Core.Ty} {nativeWorld : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typed : Core.RuntimeValueHasType nativeWorld native (catalog.functionType parameter result) definitions) :
    ∃ a b, native = .pair a b := by
  unfold SourceCoreCompatibleCatalog.Catalog.functionType at typed
  split at typed <;> cases typed <;> exact ⟨_, _, rfl⟩

/-- A genuine encoded pair of represented nullary Word functions has exactly
that public shape. This derives the shape of every sufficiently fueled export. -/
theorem pair_public_shape {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {model : FunctionModel checked.catalog ambient} {sourceRegistry : SourceCoreRawMetadata.Registry}
    {sourceMap : LocationMap} {sourceWorld : StoreTyping} {source : Dynamic.Value}
    {session : Session artifact} {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {publicValue : SourceCorePublicValues.Value} {payload : Core.Value} {nativeType : Core.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (represented : ValueRep checked sourceRegistry model sourceMap sourceWorld
      (.product (.function .unit .word) (.function .unit .word)) source payload nativeType)
    (accepted : session.RawEncodedAt fuel registry
      (.product (.function .unit .word) (.function .unit .word)) publicValue encoded)
    (payloadAt : encoded.value = payload) :
    ∃ left right, publicValue = .product (.function left) (.function right) := by
  have projected := represented.projection
  have nativeEq : nativeType = .product (checked.catalog.functionType .unit .word)
      (checked.catalog.functionType .unit .word) := by
    simpa [SourceCoreCompatibleCatalog.Catalog.project] using (Except.ok.inj projected).symm
  have typed := represented.runtime_hasType
  rw [nativeEq] at typed
  cases typed with
  | pair firstTyped secondTyped =>
      obtain ⟨left, right, publicEq⟩ := encoded_pair_shape accepted ⟨_, _, payloadAt⟩
      subst publicValue
      obtain ⟨remaining, _fuelEq, first, second, firstAt, secondAt, encodedEq⟩ := accepted.product rfl
      rw [encodedEq] at payloadAt
      have payloads := Core.Value.pair.inj payloadAt
      obtain ⟨leftHandle, leftEq⟩ := encoded_function_shape firstAt
        (payloads.1.symm ▸ native_function_pair firstTyped)
      obtain ⟨rightHandle, rightEq⟩ := encoded_function_shape secondAt
        (payloads.2.symm ▸ native_function_pair secondTyped)
      exact ⟨leftHandle, rightHandle, by rw [leftEq, rightEq]⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev DirectCall := Tests.SourceCoreRecursiveIndex.DirectCall
abbrev IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :=
  Tests.SourceCoreRecursiveIndex.IdentityShape function signature .word
abbrev closureType : TypeSystem.Ty := .function .unit .word
abbrev factoryType : TypeSystem.Ty := .product closureType closureType
private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)
private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]


structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Read function.typedBody binder .word
  call : DirectCall function.typedBody identity read.node.id .word .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = .word

def RelayShape.nodeList {function signature identity} (shape : RelayShape function signature identity) : List SourceInference.Node :=
  [.expression shape.read.node, .expression shape.call.callee.node, .expression shape.call.value.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let returned : StatementFacts := {type:=.word, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.singleton returned, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have called := shape.call.typed (fields ▸ identityMember) word read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm called shape.statementType)⟩

structure LambdaShape (function : CheckedFunction) (identity : ProgramFunctionSignature) (binder : TypedBinder) where
  read : Read function.typedBody binder .word
  call : DirectCall function.typedBody identity read.node.id .word .word
  innerReturn : StatementNode
  expression : ExpressionNode
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some call.value.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  lambda : expression.form = .lambda [] .word [innerReturn.id]
  expressionRaw : expression.rawType = closureType
  expressionType : expression.type = closureType
  requirements : expression.requirements = []
  coercions : expression.coercions = []

def LambdaShape.nodeList {function identity binder} (shape : LambdaShape function identity binder) : List SourceInference.Node :=
  [.expression shape.read.node, .expression shape.call.callee.node, .expression shape.call.value.node,
   .statement shape.innerReturn, .expression shape.expression]

structure FactoryShape (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody relay initialRead.node.id .word .word
  left : LambdaShape function identity localBinder
  right : LambdaShape function identity localBinder
  initialized : StatementNode
  tupleNode : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType, closureType]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  localOrdinary : localBinder.comptime = false
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some initial.value.node.id)
  initializedType : initialized.type = .unit
  tupleFound : function.typedBody.lookupExpression? tupleNode.id = some tupleNode
  tupleForm : tupleNode.form = .tuple [left.expression.id, right.expression.id]
  tupleRaw : tupleNode.rawType = factoryType
  tupleType : tupleNode.type = factoryType
  tupleRequirements : tupleNode.requirements = []
  tupleCoercions : tupleNode.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  returnStatement : statement.form = .returnStmt (some tupleNode.id)
  statementType : statement.type = factoryType

def FactoryShape.nodeList {function signature identity relay} (shape : FactoryShape function signature identity relay) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
   .statement shape.initialized] ++ shape.left.nodeList ++ shape.right.nodeList ++
   [.expression shape.tupleNode, .statement shape.statement]

theorem FactoryShape.statementTyping {function signature identity relay}
    (shape : FactoryShape function signature identity relay) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (relayMember : relay ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  let returned : StatementFacts := {type:=factoryType, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton returned), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    let locals := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.localOwner
          scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
          quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.localRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localDistinct]
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have initial := shape.initial.typed (fields ▸ relayMember) word initialRead
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible locals closureType := ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have lambdaTyped (lambda : LambdaShape function identity shape.localBinder) :
        ExpressionHasType function.typedBody locals lambda.expression.id closureType := by
      have read := lambda.read.typed shape.localScheme shape.localRequirements localWord
        localExtended.local_self localExtended.local_scheme_requirements_self
      have called := lambda.call.typed (show identity ∈ locals.signatures.functions from fields ▸ identityMember) localWord read
      rw [← lambda.expressionType]
      refine .intro (lookupExpression?_sound lambda.expressionFound)
        (lambda.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound lambda.innerReturnFound)
            lambda.innerReturnForm called lambda.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) lambda.expressionRaw callable (lambda.expressionType ▸ callable) ?_
      rw [lambda.requirements, lambda.coercions, lambda.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have pair : TypeAdmissible locals factoryType :=
      ⟨binders, .product (.function (.builtin .unit) (.builtin .word)) (.function (.builtin .unit) (.builtin .word))⟩
    have expressionTyped : ExpressionHasType function.typedBody locals shape.tupleNode.id factoryType := by
      rw [← shape.tupleType]
      refine .intro (lookupExpression?_sound shape.tupleFound)
        (shape.tupleForm ▸ ExpressionFormHasRawType.tuple (.cons (lambdaTyped shape.left) (.cons (lambdaTyped shape.right) (.nil _))))
        shape.tupleRaw pair (shape.tupleType ▸ pair) ?_
      rw [shape.tupleRequirements, shape.tupleCoercions, shape.tupleType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initialized : StatementHasType function.typedBody ⟨factoryType,0⟩ lexical shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initialized (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType))⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) : IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression readNode, .expression callee, .expression value, .statement statement] := function.typedBody.nodes | throw (IO.userError "relay nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let call ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity read.node.id callee value .word .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "formation parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "formation inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "formation returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "formation inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "formation binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "formation roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "formation statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "formation statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "formation statementType"
  return {binder, read, call, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, statementFound, statementForm, statementType}

def observeLambda (function : CheckedFunction) (identity : ProgramFunctionSignature) (binder : TypedBinder)
    (readNode callee value : ExpressionNode) (innerReturn : StatementNode) (expression : ExpressionNode) :
    IO (LambdaShape function identity binder) := do
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let call ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity read.node.id callee value .word .word
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "formation innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some call.value.node.id)) "formation innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "formation innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "formation expressionFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "formation lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType) "formation expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = closureType) "formation expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "formation requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "formation coercions"
  return {
    read := read
    call := call
    innerReturn := innerReturn
    expression := expression
    innerReturnFound := innerReturnFound
    innerReturnForm := innerReturnForm
    innerReturnType := innerReturnType
    expressionFound := expressionFound
    lambda := lambda
    expressionRaw := expressionRaw
    expressionType := expressionType
    requirements := requirements
    coercions := coercions
  }

def observeFactory (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) : IO (FactoryShape function signature identity relay) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "make inputs")
  let [.expression initialReadNode, .expression initialCallee, .expression initialValue, .statement initialized, .expression leftRead, .expression leftCallee, .expression leftValue, .statement leftReturn, .expression leftExpression, .expression rightRead, .expression rightCallee, .expression rightValue, .statement rightReturn, .expression rightExpression, .expression tupleNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "make nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "make local")



  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder initialReadNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay initialRead.node.id initialCallee initialValue .word .word
  let left ← observeLambda function identity localBinder leftRead leftCallee leftValue leftReturn leftExpression
  let right ← observeLambda function identity localBinder rightRead rightCallee rightValue rightReturn rightExpression
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "formation parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "formation inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType, closureType]) "formation returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "formation inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "formation binderRequirements"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "formation localScheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "formation localRequirements"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "formation localOwner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "formation localDistinct"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "formation localOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "formation roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "formation initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initial.value.node.id)) "formation initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "formation initializedType"
  let ⟨tupleFound⟩ ← observed (function.typedBody.lookupExpression? tupleNode.id = some tupleNode) "factory tuple found"
  let ⟨tupleForm⟩ ← observed (tupleNode.form = .tuple [left.expression.id, right.expression.id]) "factory tuple form"
  let ⟨tupleRaw⟩ ← observed (tupleNode.rawType = factoryType) "factory tuple raw type"
  let ⟨tupleType⟩ ← observed (tupleNode.type = factoryType) "factory tuple type"
  let ⟨tupleRequirements⟩ ← observed (tupleNode.requirements = []) "factory tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tupleNode.coercions = []) "factory tuple coercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "formation statementFound"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some tupleNode.id)) "formation returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = factoryType) "formation statementType"
  return {
    binder := binder
    localBinder := localBinder
    initialRead := initialRead
    initial := initial
    left := left
    right := right
    initialized := initialized
    tupleNode := tupleNode
    statement := statement
    parameters := parameters
    inputTypes := inputTypes
    returns := returns
    inputs := inputs
    binderRequirements := binderRequirements
    localScheme := localScheme
    localRequirements := localRequirements
    localOwner := localOwner
    localDistinct := localDistinct
    localOrdinary := localOrdinary
    roots := roots
    initializedFound := initializedFound
    initializedForm := initializedForm
    initializedType := initializedType
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRaw := tupleRaw
    tupleType := tupleType
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    statementFound := statementFound
    returnStatement := returnStatement
    statementType := statementType
  }

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function relay(value: Word) returns (Word) { return identity(value); } function make(seed: Word) returns (function() returns (Word), function() returns (Word)) { let saved: Word = relay(seed); return (lam() { return identity(saved); }, lam() { return identity(saved); }); }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, relayFunction, makeFunction]
  signatures : program.signatures.functions = [identitySignature, relaySignature, makeSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  relayMake : relaySignature.id ≠ makeSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  relayShape : RelayShape relayFunction relaySignature identitySignature
  makeShape : FactoryShape makeFunction makeSignature identitySignature relaySignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, relayFunction, makeFunction], [identitySignature, relaySignature, makeSignature] =>
      let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityFunction identitySignature .word
      let relayShape ← observeRelay relayFunction relaySignature identitySignature
      let makeShape ← observeFactory makeFunction makeSignature identitySignature relaySignature
      let ⟨methods⟩ ← observed (program.methods = []) "scoped methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "identityRelay"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "identityMake"
      let ⟨relayMake⟩ ← observed (relaySignature.id ≠ makeSignature.id) "relayMake"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity nodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures])
          · exact False.elim (relayMake (relayDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact False.elim (relayMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction, relayFunction, makeFunction, identitySignature, relaySignature, makeSignature, functions, signatures, methods, identityDeclaration, relayDeclaration, makeDeclaration, identityRelay, identityMake, relayMake, identityShape, relayShape, makeShape, identityNodes, relayNodes, makeNodes }
    | _, _ => throw (IO.userError "scoped declaration count")

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let seeds := [SourceCompiler.Seed.declaration checked.identitySignature.id,
    SourceCompiler.Seed.declaration checked.makeSignature.id, SourceCompiler.Seed.declaration checked.relaySignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedMetadata.instantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩



/-- Each observation refers to an actual compiler row, unique physical slot,
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  assumptions : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨assumptions⟩ ← observed (row.assumptions = []) "direct row assumptions"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          assumptions := assumptions
          ordinary := ordinary
          inputsOrdinary := by
            intro binder member
            have selected := List.all_eq_true.mp ordinaryInputs binder member
            cases same : binder.comptime <;> simp_all
          target := target
          global := global
          index := index
          slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
          globalKey := globalKey
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

structure ObservedProgram (fixture : CompiledFixture) where
  identityRow : ObservedRow fixture fixture.identitySignature
  makeRow : ObservedRow fixture fixture.makeSignature
  relayRow : ObservedRow fixture fixture.relaySignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 3
  identityMake : identityRow.index ≠ makeRow.index
  identityRelay : identityRow.index ≠ relayRow.index
  makeRelay : makeRow.index ≠ relayRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature fixture.identitySignature fixture.relaySignature
  relayShape : RelayShape relayRow.row.function fixture.relaySignature fixture.identitySignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  makeNodes : makeRow.row.function.typedBody.nodes = makeShape.nodeList
  relayNodes : relayRow.row.function.typedBody.nodes = relayShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let makeRow ← observeRow fixture fixture.makeSignature
  let relayRow ← observeRow fixture fixture.relaySignature
  let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityRow.row.function fixture.identitySignature .word
  let makeShape ← observeFactory makeRow.row.function fixture.makeSignature fixture.identitySignature fixture.relaySignature
  let relayShape ← observeRelay relayRow.row.function fixture.relaySignature fixture.identitySignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 3) "direct compiled globalsLength"
  let ⟨identityMake⟩ ← observed (identityRow.index ≠ makeRow.index) "direct compiled identityMake"
  let ⟨identityRelay⟩ ← observed (identityRow.index ≠ relayRow.index) "direct compiled identityRelay"
  let ⟨makeRelay⟩ ← observed (makeRow.index ≠ relayRow.index) "direct compiled makeRelay"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "direct compiled identityNodes"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = makeShape.nodeList) "direct compiled makeNodes"
  let ⟨relayNodes⟩ ← observed (relayRow.row.function.typedBody.nodes = relayShape.nodeList) "direct compiled relayNodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "direct compiled noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "direct compiled profile"
  return {identityRow, makeRow, relayRow, identityShape, makeShape, relayShape, globalsLength, identityMake, identityRelay, makeRelay, identityNodes, makeNodes, relayNodes, noLocals, profile}

/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- All three real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (identityInput makeInput relayInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ makeInput.row = observed.makeRow.row ∧ relayInput.row = observed.relayRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (relayPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (makeHeader : ActualHeader fixture observed.makeRow.row)
        (relayHeader : ActualHeader fixture observed.relayRow.row),
        identityHeader.header = identityPacket.header ∧ makeHeader.header = makePacket.header ∧ relayHeader.header = relayPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons identityPacket (.cons makePacket (.cons relayPacket .nil)))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨relayInput, relayRow, relayPacket, relayHeader, relayEq, relaySlot, relaySignature⟩ := observed.relayRow.issue
  refine ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .tail _ (.head _)
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨relayHeader.header, ?_, relaySlot.trans same.symm, ?_⟩
    · rw [relayEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.relayRow.slot.selected] at found
      exact relaySignature.trans (Option.some.inj found)

structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  left : SourceCorePublicValues.Handle
  right : SourceCorePublicValues.Handle
  returned : completion.value = .product (.function left) (.function right)

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .product (.function left) (.function right) =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, left, right, returned⟩
        | _ => throw (IO.userError "factory output was not a pair of function handles")


theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.identityRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.identityNodes, Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.identityShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.relay_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.relayRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.relayNodes, RelayShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  all_goals try cases same
  · rw [observed.relayShape.read.form] at form; cases form
  · rw [observed.relayShape.call.calleeForm] at form; cases form
  · rw [observed.relayShape.call.form] at form; cases form


private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ObservedProgram.make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.initialRead.node ∨ node = observed.makeShape.initial.callee.node ∨ node = observed.makeShape.initial.value.node ∨ node = observed.makeShape.left.read.node ∨ node = observed.makeShape.left.call.callee.node ∨ node = observed.makeShape.left.call.value.node ∨ node = observed.makeShape.left.expression ∨ node = observed.makeShape.right.read.node ∨ node = observed.makeShape.right.call.callee.node ∨ node = observed.makeShape.right.call.value.node ∨ node = observed.makeShape.right.expression ∨ node = observed.makeShape.tupleNode := by
  have present := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at present
  simpa only [FactoryShape.nodeList, LambdaShape.nodeList, List.mem_append, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false, or_assoc] using present

theorem ObservedProgram.make_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.makeRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.requirements
    · exact observed.makeShape.initial.callee.requirements
    · exact observed.makeShape.initial.value.requirements
    · exact observed.makeShape.left.read.requirements
    · exact observed.makeShape.left.call.callee.requirements
    · exact observed.makeShape.left.call.value.requirements
    · exact observed.makeShape.left.requirements
    · exact observed.makeShape.right.read.requirements
    · exact observed.makeShape.right.call.callee.requirements
    · exact observed.makeShape.right.call.value.requirements
    · exact observed.makeShape.right.requirements
    · exact observed.makeShape.tupleRequirements
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.coercions
    · exact observed.makeShape.initial.callee.coercions
    · exact observed.makeShape.initial.value.coercions
    · exact observed.makeShape.left.read.coercions
    · exact observed.makeShape.left.call.callee.coercions
    · exact observed.makeShape.left.call.value.coercions
    · exact observed.makeShape.left.coercions
    · exact observed.makeShape.right.read.coercions
    · exact observed.makeShape.right.call.callee.coercions
    · exact observed.makeShape.right.call.value.coercions
    · exact observed.makeShape.right.coercions
    · exact observed.makeShape.tupleCoercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.initialRead.form] at form; cases form
    · rw [observed.makeShape.initial.calleeForm] at form; cases form
    · rw [observed.makeShape.initial.form] at form; cases form
    · rw [observed.makeShape.left.read.form] at form; cases form
    · rw [observed.makeShape.left.call.calleeForm] at form; cases form
    · rw [observed.makeShape.left.call.form] at form; cases form
    · rw [observed.makeShape.left.lambda] at form; cases form
    · rw [observed.makeShape.right.read.form] at form; cases form
    · rw [observed.makeShape.right.call.calleeForm] at form; cases form
    · rw [observed.makeShape.right.call.form] at form; cases form
    · rw [observed.makeShape.right.lambda] at form; cases form
    · rw [observed.makeShape.tupleForm] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.read.node ∨ node = observed.relayShape.call.callee.node ∨ node = observed.relayShape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.relayRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · exact observed.relayShape.read.requirements
    · exact observed.relayShape.call.callee.requirements
    · exact observed.relayShape.call.value.requirements
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · exact observed.relayShape.read.coercions
    · exact observed.relayShape.call.callee.coercions
    · exact observed.relayShape.call.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · rw [observed.relayShape.read.form] at form; cases form
    · rw [observed.relayShape.call.calleeForm] at form; cases form
    · rw [observed.relayShape.call.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem DirectCall.syntax {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {parameter result : TypeSystem.Ty}
    (call : DirectCall source signature argument parameter result)
    (child : GeneralSyntax source argument) : GeneralSyntax source call.value.node.id := by
  refine .direct call.value.found call.form ?_ ?_
  · rw [call.exact]; exact ⟨rfl, rfl⟩
  · intro id member
    cases List.mem_singleton.mp member
    exact child

theorem LambdaShape.syntax {function : CheckedFunction} {identity : ProgramFunctionSignature}
    {binder : TypedBinder} (shape : LambdaShape function identity binder) :
    GeneralSyntax function.typedBody shape.call.value.node.id :=
  shape.call.syntax (.leaf (.read shape.read.found shape.read.form))

theorem ObservedProgram.make_initial_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.initial.value.node.id :=
  observed.makeShape.initial.syntax (.leaf (.read observed.makeShape.initialRead.found observed.makeShape.initialRead.form))

theorem ObservedProgram.relay_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.relayRow.row.function.typedBody observed.relayShape.call.value.node.id :=
  observed.relayShape.call.syntax (.leaf (.read observed.relayShape.read.found observed.relayShape.read.form))

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationLeafSupport
/-! The actual identity row is a compiler-produced read body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem identity_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.identityRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.identityShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.identityNodes] at present
  simpa only [Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.identity_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [identity_expression observed found, observed.identityShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.identityShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.identity_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.identityShape.read.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.identity_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.identity_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.identity_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.identityShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.identityShape.read.node.id
    observed.identityShape.statement observed.identityShape.roots observed.identityShape.statementFound observed.identityShape.statementForm
  exact ⟨terminal, expression, ActualHeader.identity_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

theorem ActualHeader.relay_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      actual.header.function.source observed.relayShape.call.value.node.id := by
  rw [actual.source]; exact observed.relay_syntax

theorem ActualHeader.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    (named : CallableIndexedNamedGeneration.Named) (same : named.specialized = observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  rw [actual.source]
  exact observed.relay_metadata named (by rw [same]; exact observed.relayRow.assumptions)

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.relay_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.relayShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.relayShape.call.value.node.id
    observed.relayShape.statement observed.relayShape.roots observed.relayShape.statementFound observed.relayShape.statementForm
  have same : terminal.prepared.named.specialized = observed.relayRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (actual.relay_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.relay_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "captured reuse public call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "captured reuse public call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedPairCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  left : SourceCorePublicValues.Handle
  right : SourceCorePublicValues.Handle
  returned : completion.value = .product (.function left) (.function right)
  leftType : left.sourceType = closureType
  rightType : right.sourceType = closureType

def observePairCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedPairCall session key arguments) := do
  let call ← observeCall session key arguments
  match returned : call.completion.value with
  | .product (.function left) (.function right) =>
    if leftType : left.sourceType = closureType then
      if rightType : right.sourceType = closureType then return ⟨call, left, right, returned, leftType, rightType⟩
      else throw (IO.userError "second exported closure raw type")
    else throw (IO.userError "first exported closure raw type")
  | _ => throw (IO.userError "expected two function exports")

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  firstLeftType : first.left.sourceType = closureType
  firstRightType : first.right.sourceType = closureType
  firstRead : ObservedInvocation first.completion.session first.left .unit
  firstValue : firstRead.completion.value = .word seed
  second : ObservedPairCall firstRead.completion.session observed.makeRow.row.key [.word secondSeed]
  firstDistinct : first.left ≠ first.right
  secondDistinct : second.left ≠ second.right
  distinct : first.left ≠ second.left
  secondRead : ObservedInvocation second.completion.session first.right .unit
  secondValue : secondRead.completion.value = .word seed
  thirdRead : ObservedInvocation secondRead.completion.session second.left .unit
  thirdValue : thirdRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation thirdRead.completion.session first.left .unit
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let ⟨firstLeftType⟩ ← if actual : first.left.sourceType = closureType then
    pure (PLift.up actual) else throw (IO.userError "first left closure type")
  let ⟨firstRightType⟩ ← if actual : first.right.sourceType = closureType then
    pure (PLift.up actual) else throw (IO.userError "first right closure type")
  let firstRead ← observeInvocation first.completion.session first.left .unit
  if firstValue : firstRead.completion.value = .word seed then
    let second ← observePairCall firstRead.completion.session observed.makeRow.row.key [.word secondSeed]
    if firstDistinct : first.left ≠ first.right then
      if secondDistinct : second.left ≠ second.right then
        if distinct : first.left ≠ second.left then
          let secondRead ← observeInvocation second.completion.session first.right .unit
          if secondValue : secondRead.completion.value = .word seed then
            let thirdRead ← observeInvocation secondRead.completion.session second.left .unit
            if thirdValue : thirdRead.completion.value = .word secondSeed then
              let repeatedRead ← observeInvocation thirdRead.completion.session first.left .unit
              if repeatedValue : repeatedRead.completion.value = .word seed then
                return {first, firstLeftType, firstRightType, firstRead, firstValue, second, firstDistinct, secondDistinct, distinct, secondRead, secondValue, thirdRead, thirdValue, repeatedRead, repeatedValue}
              else throw (IO.userError "first captured cell changed")
            else throw (IO.userError "second factory capture changed")
          else throw (IO.userError "second output of first factory capture changed")
        else throw (IO.userError "factory calls reused one handle")
      else throw (IO.userError "second factory returned equal handles")
    else throw (IO.userError "first factory returned equal handles")
  else throw (IO.userError "first factory capture changed")

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, makeHeader.header, relayHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have headerKey := (selected_key selected).trans key
  rcases List.mem_cons.mp selected.member with same | rest
  · rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.identityRow.keys_ne observed.makeRow observed.identityMake headerKey)
  · rcases List.mem_cons.mp rest with same | rest
    · exact same
    · have same := List.mem_singleton.mp rest
      rw [same, relayHeader.key] at headerKey
      exact False.elim (observed.makeRow.keys_ne observed.relayRow observed.makeRelay headerKey.symm)

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

theorem selected_make_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, makeHeader.header, relayHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root identityHeader makeHeader relayHeader request.selected (started_key request)

private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.identity_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.identityShape.returns]
  rfl

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.make_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = factoryType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.relay_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.relayShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.relay_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.relay_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.relay_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.relayShape.returns]
  rfl

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original


theorem ObservedProgram.make_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.localBinder.id = .ok observed.makeShape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, LambdaShape.nodeList, observed.makeShape.initialRead.form,
    observed.makeShape.initial.calleeForm, observed.makeShape.initial.form,
    observed.makeShape.left.read.form, observed.makeShape.left.call.calleeForm, observed.makeShape.left.call.form,
    observed.makeShape.right.read.form, observed.makeShape.right.call.calleeForm, observed.makeShape.right.call.form,
    observed.makeShape.initializedForm, observed.makeShape.left.innerReturnForm, observed.makeShape.left.lambda,
    observed.makeShape.right.innerReturnForm, observed.makeShape.right.lambda, observed.makeShape.tupleForm,
    observed.makeShape.returnStatement, observed.makeShape.localOwner, Ne.symm observed.makeShape.localDistinct,
    observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.localRequirements]

theorem ObservedProgram.make_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.makeRow.row.function.typedBody true
      [observed.makeShape.initialized.id, observed.makeShape.statement.id] :=
  .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
    (.returnValue [] observed.makeShape.statementFound observed.makeShape.returnStatement)

theorem ObservedProgram.make_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (unique : NodeOccurrencesUnique observed.makeRow.row.function.typedBody)
    {approved : ExpressionId → Prop} (initial : approved observed.makeShape.initial.value.node.id)
    (formation : approved observed.makeShape.tupleNode.id)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType observed.makeRow.row.function.typedBody {returnType := factoryType} context
      [observed.makeShape.initialized.id, observed.makeShape.statement.id] final facts) :
    GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved context
      (.statements true [observed.makeShape.initialized.id, observed.makeShape.statement.id]) factoryType := by
  obtain ⟨middle, firstFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.makeShape.initializedFound first
  rw [observed.makeShape.initializedForm] at firstForm
  have remaining : GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved middle
      (.statements true [observed.makeShape.statement.id]) factoryType := by
    obtain ⟨_, _, _, returned, _⟩ := head_tail tail
    have actual := form_at unique observed.makeShape.statementFound returned
    rw [observed.makeShape.returnStatement] at actual
    cases actual with
    | returnValue expression =>
      exact .body (.returnValue [] observed.makeShape.statementFound observed.makeShape.returnStatement
        observed.makeShape.statementType observed.makeShape.tupleFound observed.makeShape.tupleType
        (by simpa only [observed.makeShape.tupleType] using expression) formation)
  cases firstForm with
  | letInitialized value mono extended =>
    exact .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
      observed.make_local_declaration mono extended
      (by simp [observed.makeShape.inputs, Ne.symm observed.makeShape.localDistinct])
      observed.makeShape.initial.value.found
      (by rw [observed.makeShape.initial.value.type, observed.makeShape.localScheme]; rfl)
      (by simpa only [observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.initial.value.type] using value)
      initial remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [observed.makeShape.localScheme]; rfl))

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationMakeSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
structure ObservedLambda (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (shape : LambdaShape observed.makeRow.row.function fixture.identitySignature observed.makeShape.localBinder) where
  owned : shape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody shape.expression.id = .ok (shape.expression, reported)

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  left : ObservedLambda fixture observed observed.makeShape.left
  right : ObservedLambda fixture observed observed.makeShape.right
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeLambdaRead (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (shape : LambdaShape observed.makeRow.row.function fixture.identitySignature observed.makeShape.localBinder) :
    IO (ObservedLambda fixture observed shape) := do
  let ⟨owned⟩ ← confirm (shape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "tuple lambda owner"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody shape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = shape.expression) "exact tuple lambda read"
    return ⟨owned, reported, by simpa only [same] using read⟩

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let left ← observeLambdaRead fixture observed observed.makeShape.left
  let right ← observeLambdaRead fixture observed observed.makeShape.right
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "tuple factory seed type"
  return ⟨left, right, binderScheme⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayHeader.prepared.same

theorem ObservedProgram.cached_rows {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized = observed.identityRow.row ∨
    named.specialized = observed.makeRow.row ∨
    named.specialized = observed.relayRow.row := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact relayHeader.prepared.same

theorem ObservedProgram.cached_assumptions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized.assumptions = [] := by
  rcases observed.cached_rows identityHeader makeHeader relayHeader selected with same | same | same
  · rw [same]; exact observed.identityRow.assumptions
  · rw [same]; exact observed.makeRow.assumptions
  · rw [same]; exact observed.relayRow.assumptions

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    ∃ shape : LambdaShape observed.makeRow.row.function fixture.identitySignature observed.makeShape.localBinder,
      shape ∈ [observed.makeShape.left, observed.makeShape.right] ∧
      parameters = [] ∧ result = .word ∧ body = [shape.innerReturn.id] := by
  rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.makeShape.initialRead.form] at form; cases form
  · rw [observed.makeShape.initial.calleeForm] at form; cases form
  · rw [observed.makeShape.initial.form] at form; cases form
  · rw [observed.makeShape.left.read.form] at form; cases form
  · rw [observed.makeShape.left.call.calleeForm] at form; cases form
  · rw [observed.makeShape.left.call.form] at form; cases form
  · rw [observed.makeShape.left.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨observed.makeShape.left, by simp, parametersEq.symm, resultEq.symm, bodyEq.symm⟩
  · rw [observed.makeShape.right.read.form] at form; cases form
  · rw [observed.makeShape.right.call.calleeForm] at form; cases form
  · rw [observed.makeShape.right.call.form] at form; cases form
  · rw [observed.makeShape.right.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨observed.makeShape.right, by simp, parametersEq.symm, resultEq.symm, bodyEq.symm⟩
  · rw [observed.makeShape.tupleForm] at form; cases form

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor


theorem ActualHeader.make_body {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.function.body = [observed.makeShape.initialized.id, observed.makeShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.makeShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

def ActualHeader.make_lambda {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {shape : LambdaShape observed.makeRow.row.function fixture.identitySignature observed.makeShape.localBinder}
    (extra : ObservedLambda fixture observed shape) (actual : ActualHeader fixture observed.makeRow.row) :
    CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.ReturnLambda actual.header shape.expression.id := {
  node := shape.expression, reported := extra.reported, parameters := [], result := .word
  statement := shape.innerReturn.id, returnNode := shape.innerReturn
  expression := shape.call.value.node.id
  found := by rw [actual.source]; exact shape.expressionFound
  form := shape.lambda
  owner := by rw [actual.source]; exact extra.owned
  requirements := shape.requirements, coercions := shape.coercions
  ordinary := by simp only [observed.noLocals, List.find?_nil]
  read := by rw [actual.source]; exact extra.read
  returnFound := by rw [actual.source]; exact shape.innerReturnFound
  returnForm := shape.innerReturnForm, returnType := shape.innerReturnType }

def ActualHeader.make_container {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Container actual.header observed.makeShape.tupleNode.id := {
  node := observed.makeShape.tupleNode
  found := by rw [actual.source]; exact observed.makeShape.tupleFound
  requirements := observed.makeShape.tupleRequirements
  coercions := observed.makeShape.tupleCoercions
  ordinary := by simp only [observed.noLocals, List.find?_nil] }

theorem ActualHeader.make_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    GenericImperativeMatch.Syntax actual.header.function.source
      (CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Syntax actual.header) actual.header.context
      (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.makeShape.roots, actual.make_result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.make_body, actual.make_result_type]
  apply observed.make_body_syntax (actual.source ▸ actual.header.unique) _ _ typed
  · apply CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Syntax.general
    rw [actual.source]; exact observed.make_initial_syntax
  · refine .tuple actual.make_container observed.makeShape.tupleForm ?_
    intro child member
    rcases List.mem_cons.mp member with same | remaining
    · subst child; exact .formation (actual.make_lambda extra.left)
    · cases List.mem_singleton.mp remaining
      exact .formation (actual.make_lambda extra.right)

theorem ActualHeader.make_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.make_body]
  exact observed.make_body_shape

def ActualHeader.make_body_packet {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.makeRow.row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation observed.makeRow.row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .canonicalBranching receipt }

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry actual.header
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) body
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨receipt⟩ := actual.make_receipt
  refine ⟨⟨actual.make_body_packet receipt, ?_⟩⟩
  apply CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.of_actual
    actual.prepared actual.aligned fixture.recipePrepared actual.diagnostic receiver
    fixture.source_wellFormed observed.profile _ rows complete (bootstrap_zero fixture.recipe.compiled)
    observed.makeRow.entryMember receipt stagePrepared (actual.make_syntax extra)
  rw [actual.source]
  exact .of_ordinary (observed.make_metadata actual.prepared.named
    (by rw [actual.prepared.same]; exact observed.makeRow.assumptions))

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader relayHeader support.caller.selected with original | original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.relay_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    obtain ⟨shape, _member, _parameters, _result, bodyShape⟩ := observed.make_lambda_shape found code.sourceForm
    have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
        function.source shape.call.value.node.id function.body := by
      rw [bodyShape]
      exact .returning [] (by rw [sameSource]; exact shape.innerReturnFound)
        shape.innerReturnForm
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader relayHeader support.caller.selected))
    have tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        function.source shape.call.value.node.id := by
      rw [sameSource]; exact shape.syntax
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, canonical⟩ :=
      CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport.of_actual
        stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
        (signature := fixture.makeSignature)
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        (by rw [sameSource]; exact observed.makeRow.sourceOwner)
        shape.call.value.node.id terminal tree _ (.anonymous selected)
    exact ⟨⟨.canonicalTerminal packet, canonical⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  relayInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  makeRow : makeInput.row = observed.makeRow.row
  relayRow : relayInput.row = observed.relayRow.row
  identityPacket : Issued identityInput
  makePacket : Issued makeInput
  relayPacket : Issued relayInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  makeHeader : ActualHeader fixture observed.makeRow.row
  relayHeader : ActualHeader fixture observed.relayRow.row
  identityEq : identityHeader.header = identityPacket.header
  makeEq : makeHeader.header = makePacket.header
  relayEq : relayHeader.header = relayPacket.header
  rows : Inventory [identityInput, makeInput, relayInput]
  rowsEq : rows = .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, makeInput, relayInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  relayDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.identityHeader.header, support.makeHeader.header, support.relayHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.identityEq, support.makeEq, support.relayEq]

private def selectThree {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second third : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (firstSecond : first.slot ≠ second.slot) (firstThird : first.slot ≠ third.slot)
    (secondThird : second.slot ≠ third.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second) (thirdValue : property third) :
    ∀ header, header ∈ [first, second, third] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (firstSecond (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstThird (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else if secondSlot : header.slot = second.slot then
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (secondThird (secondSlot.symm.trans other))
    exact same.symm ▸ secondValue
  else
    have same : header = third := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ thirdValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have headerList : headers rows = [identityHeader.header, makeHeader.header, relayHeader.header] := by
    simp only [rows, headers, identityEq, makeEq, relayEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have identityInputIndex : identityHeader.header.slot = identityInput.prepared.index := by
    rw [identityEq]; exact identityPacket.aligned.slot
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have relayIndex : relayHeader.header.slot = observed.relayRow.index :=
    relayHeader.aligned.slot.trans (observed.relayRow.prepared_slot relayHeader.prepared).2
  have relayInputIndex : relayHeader.header.slot = relayInput.prepared.index := by
    rw [relayEq]; exact relayPacket.aligned.slot
  have identityMake : identityHeader.header.slot ≠ makeHeader.header.slot := by
    rw [identityIndex, makeIndex]
    exact observed.identityMake
  have identityMakeInput : identityInput.prepared.index ≠ makeInput.prepared.index := by
    rw [← identityInputIndex, ← makeInputIndex]
    exact identityMake
  have identityRelay : identityHeader.header.slot ≠ relayHeader.header.slot := by
    rw [identityIndex, relayIndex]
    exact observed.identityRelay
  have identityRelayInput : identityInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← identityInputIndex, ← relayInputIndex]
    exact identityRelay
  have makeRelay : makeHeader.header.slot ≠ relayHeader.header.slot := by
    rw [makeIndex, relayIndex]
    exact observed.makeRelay
  have makeRelayInput : makeInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← makeInputIndex, ← relayInputIndex]
    exact makeRelay
  obtain ⟨makeBody, makeSupport⟩ := makeHeader.make_support extra rows complete
    (registry := registry) receiver (actualStagePrepared fixture)
  obtain ⟨identityTerminal, _identityExpression, identitySupport⟩ :=
    identityHeader.identity_support observed receiver (actualStagePrepared fixture)
  obtain ⟨identitySupport⟩ := identitySupport
  obtain ⟨relayTerminal, _relayExpression, ⟨relaySupport⟩⟩ :=
    relayHeader.relay_support observed rows complete receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectThree identityMake identityRelay makeRelay property
      ⟨of_terminal identityTerminal, .recursive identitySupport⟩ ⟨makeBody, makeSupport⟩
      ⟨of_terminal relayTerminal, .canonical relaySupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    makeInput := makeInput
    relayInput := relayInput
    identityRow := identityRow
    makeRow := makeRow
    relayRow := relayRow
    identityPacket := identityPacket
    makePacket := makePacket
    relayPacket := relayPacket
    identityHeader := identityHeader
    makeHeader := makeHeader
    relayHeader := relayHeader
    identityEq := identityEq
    makeEq := makeEq
    relayEq := relayEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [identityMakeInput, identityRelayInput, makeRelayInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family identityHeader makeHeader relayHeader rows complete (actualStagePrepared fixture) receiver association
    identityDescriptor := identityHeader.descriptor identityStages
    makeDescriptor := makeHeader.descriptor makeStages
    relayDescriptor := relayHeader.descriptor relayStages }⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.makeRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.makeHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.terminals
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, _started, _parameterView, _resultView,
    _succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.terminals
      support.supports fixture.source_wellFormed state.history entry member entryType input state.atRecipe
      state.registry state.atSession (by simpa only [entryHandle] using call.executed) .skip invocation
  have addedNil : added = [] := by
    simpa only [RecursiveNamedPublicNestedOutputSelections.Selection.handles, List.map_eq_nil_iff] using _handles
  subst added
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := by simpa only [List.append_nil, PublicSupports.functions] using retained }
  exact ⟨sources, source, next, packing, sourceSize, trace⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationMakeStep
/-! A genuine successful public factory call extends the current retained
history with both actual output closures. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's two exported handles. -/
theorem RetainedState.make_pair
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedPairCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ firstEntry secondEntry : Entry,
      firstEntry.sourceType = closureType ∧ secondEntry.sourceType = closureType ∧
      firstEntry.handle = call.left ∧ secondEntry.handle = call.right ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [firstEntry, secondEntry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value (.product firstEntry.source secondEntry.source)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_make_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.makeHeader.make_input_types_source]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.makeDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, _caller, _related, _continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed descriptor
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registryAt] at returnedRegistry
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have rawType : request.header.function.resultType = .product closureType closureType := by
    rw [selected]
    exact support.makeHeader.make_result_type
  have publicPair := valueEq.symm.trans call.returned
  obtain ⟨source, payload, added, sourceValue, _nativeValue, collected, _handles, addition⟩ :=
    named_collection rfl state.atRecipe requested succeeded result returnedRegistry (.refl _)
      (pairSelection rawType publicPair)
  obtain ⟨firstEntry, secondEntry, entriesEq, sourceEq, firstType, secondType, firstHandle, secondHandle⟩ :=
    pair_selection_entries rawType publicPair collected
  subst added
  obtain ⟨caller, related, post⟩ := result.2.2.2.2.2.2.2
  have continued := RecursiveNamedPublicFunctionHistory.History.next state.history rfl request.started
    request.selected succeeded result caller ⟨related, post⟩ addition
  let after : RetainedState support call.completion.session (entries ++ [firstEntry, secondEntry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := continued }
  refine ⟨firstEntry, secondEntry, firstType, secondType, firstHandle, secondHandle, after,
    request.rawD, request.function, sourceSize, ?_, ?_⟩
  · exact selected ▸ request.sourceAt
  · exact sourceEq ▸ sourceValue ▸ trace

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationSeed
/-! Actual initialization and the first public make(10) execution establish
both Source closures and history entries, including their captured local cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ firstEntry secondEntry : Entry,
      firstEntry.sourceType = closureType ∧ secondEntry.sourceType = closureType ∧
      firstEntry.handle = first.left ∧ secondEntry.handle = first.right ∧
      ∃ state : RetainedState support first.completion.session [firstEntry, secondEntry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value (.product firstEntry.source secondEntry.source)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types_source]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.makeHeader.header support.makeInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.makePacket.header.named.specialized support.makeInput.prepared.available)) := by
    rw [support.makeEq]
    exact support.makePacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, fullResult⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.public_run_succeeded_reflects
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared fixture.recipe.compiled)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports
        support.makeHeader.header support.makeHeader.header fixture.source_wellFormed).2)
      (invocation := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
      first.started first.executed support.makeDescriptor
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  have publicPair := valueEq.symm.trans first.returned
  obtain ⟨source, payload, added, sourceValue, _nativeValue, collected, _handles, addition⟩ :=
    named_collection rfl started.recipe_eq requested succeeded fullResult returnedRegistry
      (by rw [receiver.registry]; exact .refl _)
      (pairSelection support.makeHeader.make_result_type publicPair)
  obtain ⟨firstEntry, secondEntry, entriesEq, sourceEq, firstType, secondType, firstHandle, secondHandle⟩ :=
    pair_selection_entries support.makeHeader.make_result_type publicPair collected
  subst added
  obtain ⟨returnedCaller, related, post⟩ := fullResult.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl started selected succeeded fullResult
    returnedCaller ⟨related, post⟩ addition
  let state : RetainedState support first.completion.session [firstEntry, secondEntry] := {
    artifact := artifact
    session := returnedCompletion.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  refine ⟨firstEntry, secondEntry, firstType, secondType, firstHandle, secondHandle, state, ?_⟩
  exact ⟨support.makeInput.prepared.available, _, sourceSize, sourceAt, sourceEq ▸ sourceValue ▸ trace⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationPublicExecution
/-! Two real tuple exports and four direct calls retain both output pairs in
order across the exact returned sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  third : Entry
  fourth : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  thirdType : third.sourceType = closureType
  fourthType : fourth.sourceType = closureType
  firstHandle : first.handle = sequence.first.left
  secondHandle : second.handle = sequence.first.right
  thirdHandle : third.handle = sequence.second.left
  fourthHandle : fourth.handle = sequence.second.right
  firstHandleType : sequence.first.left.sourceType = closureType
  secondHandleType : sequence.first.right.sourceType = closureType
  thirdHandleType : sequence.second.left.sourceType = closureType
  fourthHandleType : sequence.second.right.sourceType = closureType
  firstDistinct : first.handle ≠ second.handle
  secondDistinct : third.handle ≠ fourth.handle
  distinct : first.handle ≠ third.handle
  initial : RetainedState support sequence.first.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  secondState : RetainedState support sequence.second.completion.session [first, second, third, fourth]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, third, fourth]
  thirdReadState : RetainedState support sequence.thirdRead.completion.session [first, second, third, fourth]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, third, fourth]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value (.product first.source second.source)) initial.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word secondSeed] (.value (.product third.source fourth.source)) secondState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap second.source secondArguments (.value (.word seed)) secondReadState.heap
  thirdArguments : List Dynamic.Value
  thirdPacking : Dynamic.ValuesPack thirdArguments .unit
  thirdReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap third.source thirdArguments (.value (.word secondSeed)) thirdReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    thirdReadState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages relayStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, second, firstType, secondType, firstHandle, secondHandle, initial, firstTrace⟩ :=
    first_meaning support makeStages sequence.first
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word initial first
    (by simp) firstType firstHandle sequence.firstLeftType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨third, fourth, thirdType, fourthType, thirdHandle, fourthHandle, secondState, secondTrace⟩ :=
    firstReadState.make_pair sequence.second scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word secondState second
    (by simp) secondType secondHandle sequence.firstRightType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨thirdArguments, thirdReadState, thirdPacking, thirdReadTrace⟩ := invoke_word secondReadState third
    (by simp) thirdType thirdHandle sequence.second.leftType (unitInput _) sequence.thirdRead sequence.thirdValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word thirdReadState first
    (by simp) firstType firstHandle sequence.firstLeftType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, third, fourth, firstType, secondType, thirdType, fourthType,
    firstHandle, secondHandle, thirdHandle, fourthHandle,
    firstHandleType := sequence.firstLeftType
    secondHandleType := sequence.firstRightType
    thirdHandleType := sequence.second.leftType
    fourthHandleType := sequence.second.rightType
    firstDistinct := by rw [firstHandle, secondHandle]; exact sequence.firstDistinct
    secondDistinct := by rw [thirdHandle, fourthHandle]; exact sequence.secondDistinct
    distinct := by rw [firstHandle, thirdHandle]; exact sequence.distinct
    initial, firstReadState, secondState, secondReadState, thirdReadState, finalState,
    firstTrace, firstArguments, firstPacking, firstReadTrace, secondTrace,
    secondArguments, secondPacking, secondReadTrace, thirdArguments, thirdPacking, thirdReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages relayStages sequence receiver⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel factoryType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world factoryType source payload nativeType

/-- Both output functions are selected from the actual completion and enter
its retained history, with the whole represented Source result unchanged. -/
def ReturnedPair {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) (source : Dynamic.Value)
    (after : Dynamic.Heap) (fuel : Nat) : Prop :=
  ∃ first second : RecursiveNamedPublicFunctionHistory.Entry,
    first.sourceType = closureType ∧ second.sourceType = closureType ∧
    source = .product first.source second.source ∧
    completion.value = .product (.function first.handle) (.function second.handle) ∧
    ∃ state : RetainedState support completion.session (entries ++ [first, second]),
      state.heap = after ∧ ReturnedValue completion state source fuel

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedPair support completion [] source after outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader support.relayHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types_source]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  have requestedPair := support.makeHeader.make_result_type ▸ requested
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld factoryType source _payload support.makeHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.makeHeader.make_result_type] at result
    cases result with | value represented => exact represented
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := exported.reimports_payload requestedPair rfl
  obtain ⟨left, right, actualPair⟩ := pair_public_shape represented encodedAt payloadAt
  obtain ⟨actualSource, payload, added, sourceValue, _nativeValue, collected, _handles, addition⟩ :=
    named_collection rfl started.recipe_eq requested exported _fullResult registry
      (by rw [contextAt]; exact .refl _)
      (pairSelection support.makeHeader.make_result_type actualPair)
  have sameSource : source = actualSource := Staging.Recursive.Outcome.value.inj sourceValue
  obtain ⟨firstEntry, secondEntry, entriesEq, sourceEq, firstType, secondType, firstHandle, secondHandle⟩ :=
    pair_selection_entries support.makeHeader.make_result_type actualPair collected
  subst added
  obtain ⟨returnedCaller, related, post⟩ := _fullResult.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl started selected exported _fullResult
    returnedCaller ⟨related, post⟩ addition
  let returned : RetainedState support completion.session [firstEntry, secondEntry] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  refine ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr ready,
    firstEntry, secondEntry, firstType, secondType, sameSource.trans sourceEq, ?_, returned, rfl,
    _payload, _, ?_, represented⟩
  · rw [firstHandle, secondHandle]
    exact actualAt.1.trans actualPair
  · rw [actualAt.1]
    exact ⟨encoded, encodedAt, payloadAt⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationInvocationForward
/-! The four captured closure calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit .word)
    {word : Core.Word}
    (call : ObservedInvocation publicSession handle .unit)
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    (packing : Dynamic.ValuesPack arguments .unit)
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle word after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  subst nativeResult
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (support.terminals)
      support.supports fixture.source_wellFormed state.history entry member entryType
      unitInput state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started packing trace atCheckpoint
  have payloadEq : payload = .word word := by
    have represented := fullResult.1
    cases represented with
    | value related =>
      obtain ⟨actual, sourceEq, nativeEq⟩ := CompatibleExpressionPrimitives.word_fields related
      cases Dynamic.Value.word.inj sourceEq
      exact nativeEq
  subst payload
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, atCompletion,
      _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  have valueEq : completion.value = .word word := atCompletion.1.trans (exported.word_value requested)
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨completion, succeeded, valueEq, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

/-- All four actual closure invocations preserve their reached Source heap
for every sufficient resume of the original public invocation. -/
def InvocationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  ForwardWordAt meaning.support sequence.first.completion.session [meaning.first, meaning.second]
    sequence.first.left seed meaning.firstReadState.heap ∧
  ForwardWordAt meaning.support sequence.second.completion.session [meaning.first, meaning.second, meaning.third, meaning.fourth]
    sequence.first.right seed meaning.secondReadState.heap ∧
  ForwardWordAt meaning.support sequence.secondRead.completion.session [meaning.first, meaning.second, meaning.third, meaning.fourth]
    sequence.second.left secondSeed meaning.thirdReadState.heap ∧
  ForwardWordAt meaning.support sequence.thirdRead.completion.session [meaning.first, meaning.second, meaning.third, meaning.fourth]
    sequence.first.left seed meaning.finalState.heap

theorem SequenceWitness.invocations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : InvocationForwardMeaning meaning := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstReady
  have secondReady := sequence.second.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondReady
  have thirdReadReady := sequence.thirdRead.executed.exportsReady secondReadReady
  exact ⟨forward_word meaning.initial meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.firstRead firstReady
      meaning.firstPacking meaning.firstReadTrace,
    forward_word meaning.secondState meaning.second (by simp)
      meaning.secondType meaning.secondHandle meaning.secondHandleType sequence.secondRead secondReady
      meaning.secondPacking meaning.secondReadTrace,
    forward_word meaning.secondReadState meaning.third (by simp)
      meaning.thirdType meaning.thirdHandle meaning.thirdHandleType sequence.thirdRead secondReadReady
      meaning.thirdPacking meaning.thirdReadTrace,
    forward_word meaning.thirdReadState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.repeatedRead thirdReadReady
      meaning.repeatedPacking meaning.repeatedReadTrace⟩

end Tests.SourceCoreRecursiveFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveFormationForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {value : Core.Word}
    (call : ObservedPairCall session observed.makeRow.row.key [.word value])
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedPair support completion entries source after outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedPairCall session observed.makeRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have rawType : request.header.function.resultType = factoryType := by
    rw [selectedHeader]
    exact support.makeHeader.make_result_type
  have requestedPair := rawType ▸ requested
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld factoryType source payload request.header.output := by
    have result := fullResult.2.1
    rw [rawType] at result
    cases result with | value represented => exact represented
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := exported.reimports_payload requestedPair rfl
  obtain ⟨left, right, actualPair⟩ := pair_public_shape represented encodedAt payloadAt
  obtain ⟨actualSource, actualPayload, added, sourceValue, _nativeValue, collected, _handles, addition⟩ :=
    named_collection rfl state.atRecipe requested exported fullResult registry
      (by rw [contextAt]; exact .refl _)
      (pairSelection rawType actualPair)
  have sameSource : source = actualSource := Staging.Recursive.Outcome.value.inj sourceValue
  obtain ⟨firstEntry, secondEntry, entriesEq, sourceEq, firstType, secondType, firstHandle, secondHandle⟩ :=
    pair_selection_entries rawType actualPair collected
  subst added
  obtain ⟨returnedCaller, related, post⟩ := fullResult.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.next
    (RecursiveNamedPublicHistoryRegistryExtension.extend_history state.history extended)
    rfl request.started request.selected exported fullResult returnedCaller ⟨related, post⟩ addition
  let returned : RetainedState support completion.session (entries ++ [firstEntry, secondEntry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  refine ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    firstEntry, secondEntry, firstType, secondType, sameSource.trans sourceEq, ?_, returned, rfl,
    payload, _, ?_, represented⟩
  · rw [firstHandle, secondHandle]
    exact actualAt.1.trans actualPair
  · rw [actualAt.1]
    exact ⟨encoded, encodedAt, payloadAt⟩

/-- Both factories have independent public execution and output bounds. Every
sufficient output collects its two real leaves into the returned history. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first (.product meaning.first.source meaning.second.source) meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.second
    (.product meaning.third.source meaning.fourth.source) meaning.secondState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have firstReadReady := sequence.firstRead.executed.exportsReady firstReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_make meaning.firstReadState sequence.second firstReadReady meaning.secondTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver, ForwardMeaning meaning ∧ InvocationForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra identityStages makeStages relayStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward, meaning.invocations_forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let identityStages ← observeStages fixture observed.identityRow
  let makeStages ← observeStages fixture observed.makeRow
  let relayStages ← observeStages fixture observed.relayRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra identityStages makeStages relayStages sequence
  IO.println "Recursive tuple formation: make10→A,B; A10; make20→C,D; B10; C20; A10; all four exports retained, exact Source heaps/history and six public fuel bounds proved"

end Tests.SourceCoreRecursiveFormation
end
