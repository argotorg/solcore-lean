import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion

/-!
# The recursive staged profile: primitives, tuples and mappings

Staged meaning of primitives, tuples and mapping reads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
/-! Direct staged primitive correspondence over the actual compatible ambient
heap. Static support retains the original compiler tree and selected literal
rows, including the empty tuple unit leaf. Mapping lazy initialization, methods,
coercions and callable bodies remain separate. -/
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionPrimitives

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}

/-- Only real numeric selection and an actually atomic source form are retained. -/
def LiteralSupported (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧
    CompatibleExpressionLiterals.Literal solved node code.type code.expression ∧
    CompatibleExpressionLiteralRuntime.NumericSelected solved node ∧ Staging.Recursive.AtomicForm node.form

/-- The actual read receipt retains its declaration, ordered slot and raw source
binding; this support excludes the distinct mapping-initialization code. -/
def ReadSupported (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ receipt : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) code.expression,
    receipt.type = code.type ∧ CompatibleExpressionReads.StaticBinding receipt context ∧
    ¬ ∃ key value, receipt.declared.scheme.body = .mapping key value

inductive ProductSupported :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | literal {id lowered} (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered)
      (leaf : LiteralSupported (source := source) (solved := solved) id lowered) :
      ProductSupported (CompatibleExpressionProducts.Tree.literal (scope := scope) receipt)
  | read {id lowered} (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered)
      (ordinary : ReadSupported (fuel := fuel) (values := values) (source := source)
        (context := context) (reasonAt := reasonAt) (scope := scope) id lowered) :
      ProductSupported (CompatibleExpressionProducts.Tree.read (scope := scope) receipt)
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope inner lowered)
      (childSites : ProductSupported child) :
      ProductSupported (CompatibleExpressionProducts.Tree.group (scope := scope) metadata form innerFound sourceType child)
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope left first)
      (secondTree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope right second)
      (firstTreeSites : ProductSupported firstTree) (secondTreeSites : ProductSupported secondTree) :
      ProductSupported (CompatibleExpressionProducts.Tree.pair (scope := scope) metadata form leftFound rightFound sourceType firstTree secondTree)

inductive Supported :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | product {id lowered}
      (child : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : ProductSupported child) :
      Supported (Tree.product (scope := scope) child)
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered)
      (childSites : Supported child) :
      Supported (Tree.group (scope := scope) metadata form innerFound sourceType child)
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second)
      (firstTreeSites : Supported firstTree) (secondTreeSites : Supported secondTree) :
      Supported (Tree.pair (scope := scope) metadata form leftFound rightFound sourceType firstTree secondTree)
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : Tree fuel values source context solved reasonAt scope operand ⟨core.operandType, childCode⟩)
      (childSites : Supported child) :
      Supported (Tree.unary (scope := scope) metadata form found inputType outputType profile child)
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : Tree fuel values source context solved reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree fuel values source context solved reasonAt scope right ⟨mode.operandType operator, rightCode⟩)
      (firstSites : Supported first) (secondSites : Supported second) :
      Supported (Tree.binary (scope := scope) metadata form leftFound rightFound leftType rightType outputType profile first second)


variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}

/-- The ambient model is explicit; no default catalog/projection cast is used. -/
inductive Result (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty)
    (type : Ty) (faults : FunctionCalls.FaultRep) : Staging.Recursive.Outcome → Value → Prop where
  | value {source value} (represented : ValueRep values.checked registry functions mapping world sourceType source value type) :
      Result mapping world sourceType type faults (.value source) (.inRight .word value)
  | fault {reason token} (represented : faults reason token) :
      Result mapping world sourceType type faults (.fault (.semantic reason)) (.inLeft type (.word token))

/-- Reflection consumes the original completed Core derivation and returns an
independent staged source trace, including the original full final heap. -/
def Reflects (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      Result functions (registry := registry) finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

private theorem ordinary_completed {environment : Environment} {store finalStore : Store}
    {index target : Nat} {type : Ty} {reason : Word} {value optional : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : store.read? target = some optional)
    (evaluated : Evaluates environment store (OptionalCell.read type (.var index) reason) value finalStore) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ value = .inRight .word payload ∧ finalStore = store) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ value = .inLeft type (.word reason) ∧ finalStore = store) := by
  cases evaluated with
  | caseLeft loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inLeft token =>
          cases token
          exact .inr ⟨_, _, same, rfl, rfl⟩
  | caseRight loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inRight payload =>
          cases payload with
          | var samePayload =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at samePayload
            cases samePayload
            exact .inl ⟨_, _, same, rfl, rfl⟩

variable (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource uninitialized in
/-- The actual completed ordinary-cell read is inverted before a source rule
is built. Full heap representation supplies the cell's ordinary metadata. -/
theorem read_reflects :
    Reflects functions (registry := registry) program stages invocation context
      (fun current id code => ReadSupported (fuel := fuel) (values := values) (source := source)
        (context := context) (reasonAt := reasonAt) (scope := current) id code) faults := by
  intro current id lowered supported root found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨certificate, sameType, binding, notMapping⟩ := supported
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases lowered with ⟨nativeType, code⟩
  dsimp only at sameType
  subst nativeType
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  have same := Option.some.inj (metadata.found.symm.trans (sameSource ▸ found))
  subst root
  cases emitted with
  | mapping declaredType generated => exact False.elim (notMapping ⟨_, _, declaredType⟩)
  | ordinary _ =>
    obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
    obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
      GenericHeap.lookup_visible environments heaps lookup slot
    have sameCell := read.functional selectedRead
    subst selected
    have ordinary := represented.ordinary
    have result := ordinary_completed (agrees nativeLookup) nativeRead evaluated
    have contains : ContainsExpression invocation.source id node := sameSource ▸ lookupExpression?_sound metadata.found
    have atomic : Staging.Recursive.AtomicForm node.form := form ▸ .reference _ _
    cases represented with
    | initialized payload =>
      dsimp only at cellType
      rcases result with ⟨_, native, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
      · cases sameOptional
        subst value finalStore
        refine ⟨_, before, mapping, world, .atomicValue contains atomic metadata.coercions ?_,
          .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _, .refl _, .refl _ _, .refl _⟩
        rw [form, metadata.requirements]
        exact .local rfl lookup read ordinary rfl
      · cases impossible
    | uninitialized projected =>
      dsimp only at cellType
      rcases result with ⟨_, _, impossible, _⟩ | ⟨_, _, _, sameValue, sameStore⟩
      · cases impossible
      · subst value finalStore
        refine ⟨_, before, mapping, world, .atomicFault contains atomic metadata.coercions ?_,
          .fault (uninitialized id location), heaps, .refl _, .refl _, .refl _ _, .refl _⟩
        rw [form, metadata.requirements]
        exact .localUninitialized (owned := []) rfl lookup read ordinary rfl (by simpa only [cellType] using notMapping)

private inductive ScalarCode : Expr → Prop where
  | unit : ScalarCode .unit
  | bool (value) : ScalarCode (.bool value)
  | word (value) : ScalarCode (.word value)
  | integer (value) : ScalarCode (.integer value)

private theorem literal_code {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) (ξ : Renaming) :
    ∃ scalar, code.rename ξ = LanguageResult.success scalar ∧ ScalarCode scalar := by
  cases literal with
  | unit => exact ⟨_, rfl, .unit⟩
  | bool value => exact ⟨_, rfl, .bool value⟩
  | word value => exact ⟨_, rfl, .word value⟩
  | resolvedWord => exact ⟨_, rfl, .word _⟩
  | resolvedInteger => exact ⟨_, rfl, .integer _⟩

private theorem scalar_completion {scalar : Expr} (shape : ScalarCode scalar)
    {environment : Environment} {store firstStore secondStore : Store} {first second : Value}
    (one : Evaluates environment store (LanguageResult.success scalar) first firstStore)
    (two : Evaluates environment store (LanguageResult.success scalar) second secondStore) :
    first = second ∧ firstStore = secondStore := by
  cases shape <;> cases one with
  | inRight one => cases one; cases two with | inRight two => cases two; exact ⟨rfl, rfl⟩

private theorem literal_uncoerced {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

include sameSource in
theorem literal_reflects (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) :
    Reflects functions (registry := registry) program stages invocation context
      (fun _ id code => LiteralSupported (source := source) (solved := solved) id code) faults := by
  intro current id code supported root found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨node, nodeFound, literal, selected, atomic⟩ := supported
  have same := Option.some.inj (nodeFound.symm.trans (sameSource ▸ found))
  subst root
  have numeric := selected.evidence sameLedger runtime invocation.evidence
  obtain ⟨sourceValue, native, raw, payload, pure⟩ := literal.evaluates_with_evidence functions program context invocation.evidence
    numeric invocation.source environment before mapping world actual store ξ
  obtain ⟨scalar, codeEq, shape⟩ := literal_code literal ξ
  rw [codeEq] at pure evaluated
  obtain ⟨rfl, rfl⟩ := scalar_completion shape pure evaluated
  refine ⟨_, before, mapping, world,
    .atomicValue (sameSource ▸ lookupExpression?_sound nodeFound) atomic (literal_uncoerced literal) ?_,
    .value payload, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  simpa only [literal_uncoerced literal] using raw

private theorem occurrence {id : ExpressionId} {node : ExpressionNode} {type : Ty} {form : ExpressionForm}
    (metadata : Metadata values.checked source id node type) (formed : node.form = form)
    (same : invocation.source = source) : Staging.Recursive.Occurrence invocation id form :=
  ⟨node, same ▸ lookupExpression?_sound metadata.found, formed, metadata.requirements, metadata.coercions⟩

private theorem pair_rename (leftType rightType : Ty) (left right : Expr) (ξ : Renaming) :
    (LocalSequence.pair leftType rightType left right).rename ξ =
      LocalSequence.pair leftType rightType (left.rename ξ) (right.rename ξ) := by
  simp [LocalSequence.pair, LanguageResult.bind, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem fault_branch {environment : Environment} {store finalStore : Store} {reason : Word}
    {type : Ty} {value : Value}
    (evaluated : Evaluates (.word reason :: environment) store (.inLeft type (.var 0)) value finalStore) :
    value = .inLeft type (.word reason) ∧ finalStore = store := by
  cases evaluated with
  | inLeft payload =>
    cases payload with
    | var found =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      cases found
      exact ⟨rfl, rfl⟩

private theorem pair_branch {environment : Environment} {store finalStore : Store} {left right value : Value}
    (evaluated : Evaluates (right :: left :: environment) store
      (LanguageResult.success (.pair (.var 1) (.var 0))) value finalStore) :
    value = .inRight .word (.pair left right) ∧ finalStore = store := by
  cases evaluated with
  | inRight payload =>
    cases payload with
    | pair first second =>
      cases first with
      | var found =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        cases second with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          cases found
          exact ⟨rfl, rfl⟩

/-- A single code-indexed statement of reflection, used by structural IHs. -/
abbrev ReflectsCode (current : SourceCoreLocalCell.Scope) (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr) :=
  ∀ {node}, invocation.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext current environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (code.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      Result functions (registry := registry) finalMap finalWorld node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

include sameSource in
private theorem group_reflects {id inner : ExpressionId} {node innerNode : ExpressionNode}
    {code : SourceCoreBasic.LoweredExpr}
    (metadata : Metadata values.checked source id node code.type) (form : node.form = .group inner)
    (innerFound : source.lookupExpression? inner = some innerNode) (sourceType : node.type = innerNode.type)
    (child : ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope inner code) :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope id code := by
  intro root found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have same := Option.some.inj (metadata.found.symm.trans (sameSource ▸ found))
  subst root
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
    child (sameSource ▸ innerFound) environments heaps locals agrees evaluated
  exact ⟨outcome, after, finalMap, finalWorld, .group (occurrence invocation metadata form sameSource) trace,
    sourceType ▸ represented, finalHeaps, maps, worlds, frame, heapMetadata⟩

include sameSource in
private theorem pair_reflects {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode}
    {first second : SourceCoreBasic.LoweredExpr}
    (metadata : Metadata values.checked source id node (.product first.type second.type)) (form : node.form = .tuple [left, right])
    (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
    (sourceType : node.type = .product leftNode.type rightNode.type)
    (leftIH : ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope left first)
    (rightIH : ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope right second) :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope id
      ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩ := by
  intro root found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have same := Option.some.inj (metadata.found.symm.trans (sameSource ▸ found))
  subst root
  have owned := occurrence invocation metadata form sameSource
  change Evaluates actual store ((LocalSequence.pair _ _ _ _).rename ξ) value finalStore at evaluated
  rw [pair_rename] at evaluated
  cases evaluated with
  | caseLeft firstEvaluation branch =>
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      leftIH (sameSource ▸ leftFound) environments heaps locals agrees firstEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := fault_branch branch
      exact ⟨_, after, finalMap, finalWorld, .pairLeftFault owned trace, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata⟩
  | caseRight firstEvaluation branch =>
    obtain ⟨outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
      leftIH (sameSource ▸ leftFound) environments heaps locals agrees firstEvaluation
    cases represented with
    | value firstPayload =>
      cases branch with
      | caseLeft secondEvaluation branch =>
        rw [← GenericExpressionMeaning.rename_prefix] at secondEvaluation
        obtain ⟨outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH (sameSource ▸ rightFound) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees _) secondEvaluation
        cases represented with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := fault_branch branch
          exact ⟨_, after, finalMap, finalWorld, .pairRightFault owned firstTrace secondTrace, .fault matched,
            finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
      | caseRight secondEvaluation branch =>
        rw [← GenericExpressionMeaning.rename_prefix] at secondEvaluation
        obtain ⟨outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH (sameSource ▸ rightFound) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees _) secondEvaluation
        cases represented with
        | value secondPayload =>
          obtain ⟨rfl, rfl⟩ := pair_branch branch
          exact ⟨_, after, finalMap, finalWorld, .pair owned firstTrace secondTrace,
            .value (sourceType ▸ .product (firstPayload.extend (.refl registry) maps worlds) secondPayload),
            finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

include sameSource uninitialized in
private theorem product_reflects (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id code}
    (supported : ProductSupported tree) :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope id code := by
  induction supported with
  | literal receipt leaf => exact literal_reflects functions program stages invocation sameSource sameLedger runtime leaf
  | read receipt ordinary => exact read_reflects functions program stages invocation sameSource uninitialized ordinary
  | group metadata form innerFound sourceType child childSites ih =>
    exact group_reflects functions program stages invocation sameSource metadata form innerFound sourceType ih
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    exact pair_reflects functions program stages invocation sameSource metadata form leftFound rightFound sourceType firstIH secondIH

private theorem unary_branch {environment : Environment} {store finalStore : Store}
    {core : UnaryOp} {input output value : Value} (applied : core.apply input = some output)
    (evaluated : Evaluates (input :: environment) store
      (LanguageResult.success (.unary core (.var 0))) value finalStore) :
    value = .inRight .word output ∧ finalStore = store := by
  cases evaluated with
  | inRight body =>
    cases body with
    | unary operand actualApplied =>
      cases operand with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        have same := Option.some.inj (applied.symm.trans actualApplied)
        cases same
        exact ⟨rfl, rfl⟩

private theorem bind_failed {environment : Environment} {store failedStore finalStore : Store}
    {code body : Expr} {input output : Ty} {reason : Word} {value : Value}
    (child : Evaluates environment store code (.inLeft input (.word reason)) failedStore)
    (whole : Evaluates environment store (LanguageResult.bind output code body) value finalStore) :
    value = .inLeft output (.word reason) ∧ finalStore = failedStore := by
  cases whole with
  | caseLeft actual branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic child actual
    cases same
    exact fault_branch branch
  | caseRight actual _ => cases (evaluation_deterministic child actual).1

section Tail
variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {model : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {operator : Syntax.BinaryOp}
  {operand result : TypeSystem.Ty} {mode : Mode} {a b : Dynamic.Value} {x y : Value}
  {environment : Environment} {before middle finalStore : Store} {right : Expr} {value : Value}

private theorem tail_short (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked rawRegistry model mapping world operand a x (mode.operandType operator))
    {output : Dynamic.Value} (circuit : Dynamic.ShortCircuits operator a output)
    (evaluated : Evaluates (x :: environment) before (mode.tail operator right) value finalStore) :
    ∃ native, value = .inRight .word native ∧ finalStore = before ∧
      ValueRep checked rawRegistry model mapping world result output native (mode.resultType operator) := by
  cases profile with
  | word strict => cases circuit <;> cases strict
  | integer strict => cases circuit <;> cases strict
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    cases evaluated with
    | ifTrue condition branch => cases condition with | var impossible => cases impossible
    | ifFalse condition branch =>
      cases condition
      cases branch with | inRight payload => cases payload; exact ⟨_, rfl, rfl, .bool _⟩
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    cases evaluated with
    | ifFalse condition branch => cases condition with | var impossible => cases impossible
    | ifTrue condition branch =>
      cases condition
      cases branch with | inRight payload => cases payload; exact ⟨_, rfl, rfl, .bool _⟩

private theorem tail_fault (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked rawRegistry model mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a) {reason : Word}
    (child : Evaluates (x :: environment) before (right.weakenAt 0) (.inLeft (mode.operandType operator) (.word reason)) middle)
    (evaluated : Evaluates (x :: environment) before (mode.tail operator right) value finalStore) :
    value = .inLeft (mode.resultType operator) (.word reason) ∧ finalStore = middle := by
  cases profile with
  | word strict => cases strict <;> exact bind_failed child evaluated
  | integer strict => cases strict <;> exact bind_failed child evaluated
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | andTrue =>
      cases evaluated with
      | ifFalse condition branch => cases condition with | var impossible => cases impossible
      | ifTrue condition branch =>
        cases condition
        exact evaluation_deterministic branch child
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | orFalse =>
      cases evaluated with
      | ifTrue condition branch => cases condition with | var impossible => cases impossible
      | ifFalse condition branch =>
        cases condition
        exact evaluation_deterministic branch child

private theorem tail_value (profile : BinaryProfile operator operand result mode)
    (leftRep : ValueRep checked rawRegistry model mapping world operand a x (mode.operandType operator))
    (rightRep : ValueRep checked rawRegistry model mapping world operand b y (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (child : Evaluates (x :: environment) before (right.weakenAt 0) (.inRight .word y) middle)
    (evaluated : Evaluates (x :: environment) before (mode.tail operator right) value finalStore) :
    ∃ output native, Dynamic.BinaryPrimitiveApplies operator a b output ∧
      ValueRep checked rawRegistry model mapping world result output native (mode.resultType operator) ∧
      value = .inRight .word native ∧ finalStore = middle := by
  cases profile with
  | word strict =>
    have operandEq := PrimitiveExpressions.strict_operand_word strict
    obtain ⟨a, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨output, native, applied, represented, pure⟩ := word_body (functions := model) (registry := rawRegistry)
      (mapping := mapping) (world := world) strict a b
    have body : Evaluates (.word b :: .word a :: environment) middle
        (LanguageResult.success (Mode.body .word operator)) value finalStore := by
      cases strict <;> exact (LanguageResult.bind_success_iff child).mp evaluated
    cases body with
    | inRight actual =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic actual (pure _ _)
      exact ⟨_, _, applied, represented, rfl, rfl⟩
  | integer strict =>
    have operandEq : SourceCoreInteger.binaryOperandType operator = .integer := by cases strict <;> rfl
    obtain ⟨a, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨output, native, applied, represented, pure⟩ := integer_body (functions := model) (registry := rawRegistry)
      (mapping := mapping) (world := world) strict a b
    have body : Evaluates (.integer b :: .integer a :: environment) middle
        (LanguageResult.success (Mode.body .integer operator)) value finalStore := by
      cases strict <;> exact (LanguageResult.bind_success_iff child).mp evaluated
    cases body with
    | inRight actual =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic actual (pure _ _)
      exact ⟨_, _, applied, represented, rfl, rfl⟩
  | logicalAnd =>
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict => cases strict
    | andTrue =>
      cases evaluated with
      | ifFalse condition branch => cases condition with | var impossible => cases impossible
      | ifTrue condition branch =>
        cases condition
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic branch child
        exact ⟨_, _, .logicalAnd true b, .bool b, rfl, rfl⟩
  | logicalOr =>
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict => cases strict
    | orFalse =>
      cases evaluated with
      | ifTrue condition branch => cases condition with | var impossible => cases impossible
      | ifFalse condition branch =>
        cases condition
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic branch child
        exact ⟨_, _, .logicalOr false b, .bool b, rfl, rfl⟩
end Tail

include sameSource uninitialized in
theorem reflects (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
    {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (supported : Supported tree) :
    ReflectsCode functions program stages invocation (context := context) (registry := registry) (faults := faults) scope id code := by
  induction supported with
  | product child sites => exact product_reflects functions program stages invocation sameSource uninitialized sameLedger runtime sites
  | group metadata form innerFound sourceType child childSites ih =>
    exact group_reflects functions program stages invocation sameSource metadata form innerFound sourceType ih
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    exact pair_reflects functions program stages invocation sameSource metadata form leftFound rightFound sourceType firstIH secondIH
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans (sameSource ▸ found))
    subst root
    have owned := occurrence invocation metadata form sameSource
    change Evaluates actual store ((LocalPrimitiveResults.unary _ _).rename ξ) value finalStore at evaluated
    rw [unary_rename] at evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih (sameSource ▸ childFound) environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := fault_branch branch
        exact ⟨_, after, finalMap, finalWorld, .unaryOperandFault owned trace, .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih (sameSource ▸ childFound) environments heaps locals agrees childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := unary_branch coreApplied branch
        exact ⟨_, after, finalMap, finalWorld, .unary owned trace applied, .value (outputType ▸ resultRep),
          finalHeaps, maps, worlds, frame, heapMetadata⟩
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree firstSites secondSites leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans (sameSource ▸ found))
    subst root
    have owned := occurrence invocation metadata form sameSource
    change Evaluates actual store ((Mode.binary _ _ _ _).rename ξ) value finalStore at evaluated
    rw [Mode.binary_rename, Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH (sameSource ▸ leftFound) environments heaps locals agrees leftEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := fault_branch branch
        exact ⟨_, after, finalMap, finalWorld, .binaryLeftFault owned trace, .fault matched,
          finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH (sameSource ▸ leftFound) environments heaps locals agrees leftEvaluation
      cases represented with
      | value payload =>
        rw [leftType] at payload
        rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
        · obtain ⟨result, rfl, rfl, resultRep⟩ := tail_short profile payload circuit branch
          exact ⟨_, middle, middleMap, middleWorld, .binaryShortCircuit owned firstTrace circuit,
            .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
        · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
          have shifted := rightEvaluation
          rw [← GenericExpressionMeaning.rename_prefix] at shifted
          obtain ⟨outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            rightIH (sameSource ▸ rightFound) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _) shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := tail_fault profile payload continues rightEvaluation branch
            exact ⟨_, after, finalMap, finalWorld, .binaryRightFault owned firstTrace continues secondTrace,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := payload.extend (.refl registry) maps worlds
            obtain ⟨sourceResult, result, applied, resultRep, rfl, rfl⟩ := tail_value profile leftPayload rightPayload continues rightEvaluation branch
            exact ⟨_, after, finalMap, finalWorld, .binary owned firstTrace continues secondTrace applied,
              .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

/-- A structural source fragment with no invocation edge. Atomic lambda creation
is harmless here; the compiler support above still admits only actual literals
and ordinary local reads. -/
private inductive CallFree (source : TypedSource) : ExpressionId → Prop where
  | atomic {id node} (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
      (shape : Staging.Recursive.AtomicForm node.form) : CallFree source id
  | group {id node inner} (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
      (form : node.form = .group inner) (child : CallFree source inner) : CallFree source id
  | pair {id node left right} (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
      (form : node.form = .tuple [left, right]) (first : CallFree source left) (second : CallFree source right) : CallFree source id
  | unary {id node operator operand} (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
      (form : node.form = .unary operator operand) (requirements : node.requirements = []) (child : CallFree source operand) : CallFree source id
  | binary {id node left operator right} (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
      (form : node.form = .binary left operator right) (requirements : node.requirements = []) (first : CallFree source left) (second : CallFree source right) : CallFree source id

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

private theorem CallFree.no_stage {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    (free : CallFree invocation.source id) (unique : NodeOccurrencesUnique invocation.source)
    {program : Program} {stages : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {failedScope : Staging.Recursive.Scope} {call : ExpressionId} {reason : Staging.CallGuard.Fault}
    (trace : Staging.Recursive.Expression program stages invocation context environment before id
      (.fault (.stage failedScope call reason)) after) : False := by
  induction free generalizing before after with
  | atomic found empty atomic =>
    cases trace with
    | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [empty] at path
      cases path
    | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact nonempty empty
    | unaryMethod owned _ selected _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | binaryMethod owned _ selected _ _ _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
    | constructorFault owned _ =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | tupleFault owned children =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
      cases children
    | group owned child =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | pairLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | pairRightFault owned first second =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | unaryOperandFault owned child =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | binaryLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | binaryRightFault owned first continues second =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | conditional owned test branch =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | conditionalFault owned test =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | calleeFault owned child =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | rejected owned child guard =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | argumentsFault owned child guard children =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
    | applied owned uncoerced child guard children arity applies =>
      have same := occurrence_form unique found owned
      rw [same] at atomic
      cases atomic
  | group found empty form child ih =>
    cases trace with
    | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [empty] at path
      cases path
    | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact nonempty empty
    | unaryMethod owned _ selected _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryMethod owned _ selected _ _ _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
    | constructorFault owned _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | tupleFault owned children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | group owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact ih child
    | pairLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairRightFault owned first second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | unaryOperandFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryRightFault owned first continues second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditional owned test branch =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditionalFault owned test =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | calleeFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | rejected owned child guard =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | argumentsFault owned child guard children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | applied owned uncoerced child guard children arity applies =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
  | pair found empty form first second firstIH secondIH =>
    cases trace with
    | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [empty] at path
      cases path
    | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact nonempty empty
    | unaryMethod owned _ selected _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryMethod owned _ selected _ _ _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
    | constructorFault owned _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | tupleFault owned children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      cases children with
      | headFault failed => exact firstIH failed
      | tailFault first rest =>
        cases rest with
        | headFault failed => exact secondIH failed
        | tailFault second impossible => cases impossible
    | group owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact firstIH child
    | pairRightFault owned first second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact secondIH second
    | unaryOperandFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryRightFault owned first continues second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditional owned test branch =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditionalFault owned test =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | calleeFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | rejected owned child guard =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | argumentsFault owned child guard children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | applied owned uncoerced child guard children arity applies =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
  | unary found empty form requirements child ih =>
    cases trace with
    | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [empty] at path
      cases path
    | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact nonempty empty
    | unaryMethod owned _ selected _ _ _ _ _ _ _ =>
      obtain ⟨other, contains, _, actualRequirements, _⟩ := owned
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have empty := actualRequirements.symm.trans ((congrArg ExpressionNode.requirements same).trans requirements)
      rw [empty] at selected
      cases selected
    | binaryMethod owned _ selected _ _ _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
    | constructorFault owned _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | tupleFault owned children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | group owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairRightFault owned first second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | unaryOperandFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact ih child
    | binaryLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryRightFault owned first continues second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditional owned test branch =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditionalFault owned test =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | calleeFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | rejected owned child guard =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | argumentsFault owned child guard children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | applied owned uncoerced child guard children arity applies =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
  | binary found empty form requirements first second firstIH secondIH =>
    cases trace with
    | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [empty] at path
      cases path
    | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact nonempty empty
    | unaryMethod owned _ selected _ _ _ _ _ _ _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryMethod owned _ selected _ _ _ _ _ _ _ _ _ =>
      obtain ⟨other, contains, _, actualRequirements, _⟩ := owned
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have empty := actualRequirements.symm.trans ((congrArg ExpressionNode.requirements same).trans requirements)
      rw [empty] at selected
      cases selected
    | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
    | constructorFault owned _ =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | tupleFault owned children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | group owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | pairRightFault owned first second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | unaryOperandFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | binaryLeftFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact firstIH child
    | binaryRightFault owned first continues second =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
      exact secondIH second
    | conditional owned test branch =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | conditionalFault owned test =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | calleeFault owned child =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | rejected owned child guard =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | argumentsFault owned child guard children =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same
    | applied owned uncoerced child guard children arity applies =>
      have same := occurrence_form unique found owned
      rw [form] at same
      cases same

private theorem ProductSupported.callFree {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id code}
    (supported : ProductSupported tree) : CallFree source id := by
  induction supported with
  | literal receipt leaf =>
    obtain ⟨node, found, literal, _, atomic⟩ := leaf
    exact .atomic found (literal_uncoerced literal) atomic
  | read receipt ordinary =>
    obtain ⟨certificate, _, _, _⟩ := ordinary
    exact .atomic certificate.metadata.found certificate.metadata.coercions (certificate.form ▸ .reference _ _)
  | group metadata form _ _ _ _ ih => exact .group metadata.found metadata.coercions form ih
  | pair metadata form _ _ _ _ _ _ _ firstIH secondIH => exact .pair metadata.found metadata.coercions form firstIH secondIH

private theorem Supported.callFree {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (supported : Supported tree) : CallFree source id := by
  induction supported with
  | product _ sites => exact sites.callFree
  | group metadata form _ _ _ _ ih => exact .group metadata.found metadata.coercions form ih
  | pair metadata form _ _ _ _ _ _ _ firstIH secondIH => exact .pair metadata.found metadata.coercions form firstIH secondIH
  | unary metadata form _ _ _ _ _ _ ih => exact .unary metadata.found metadata.coercions form metadata.requirements ih
  | binary metadata form _ _ _ _ _ _ _ _ _ _ firstIH secondIH => exact .binary metadata.found metadata.coercions form metadata.requirements firstIH secondIH

private theorem ProductSupported.literalSites {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id code}
    (supported : ProductSupported tree) : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) := by
  induction supported with
  | literal receipt leaf => obtain ⟨node, found, literal, selected, _⟩ := leaf; exact .literal receipt ⟨node, found, literal, selected⟩
  | read receipt ordinary => exact .read receipt
  | group metadata form innerFound sourceType child childSites ih => exact .group metadata form innerFound sourceType child ih
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstIH secondIH

private theorem Supported.literalSites {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (supported : Supported tree) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) := by
  induction supported with
  | product child sites => exact .product child sites.literalSites
  | group metadata form innerFound sourceType child childSites ih => exact .group metadata form innerFound sourceType child ih
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstIH secondIH
  | unary metadata form found inputType outputType profile child childSites ih =>
    exact .unary metadata form found inputType outputType profile child ih
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH

include sameSource unique uninitialized in
/-- Preservation uses the established plain primitive proof once. The same
static support first excludes a stage failure, so erasure cannot conceal a
rejected nested invocation. Reflection above does not use this theorem. -/
theorem preserves (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
    {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (supported : Supported tree)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      Result functions (registry := registry) finalMap finalWorld node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have plain := fun (outcome : Dynamic.ExpressionOutcome)
      (evaluation : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence source environment before id outcome after) =>
    CompatibleExpressionPrimitives.preserves_with_literals functions extension program invocation.evidence unique uninitialized
    (CompatibleExpressionLiteralRuntime.preserves functions program context invocation.evidence sameLedger runtime unique faults)
    ⟨tree, supported.literalSites⟩ (sameSource ▸ found) environments heaps locals agrees evaluation
  cases outcome with
  | value value =>
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      plain _ (.value (sameSource ▸ trace.value_plain))
    cases represented with
    | value payload => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value payload, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failure =>
    cases failure with
    | semantic reason =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        plain _ (.fault (sameSource ▸ trace.semanticFault_plain))
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | stage failedScope call reason =>
      have free : CallFree invocation.source id := sameSource ▸ supported.callFree
      exact False.elim (free.no_stage (sameSource ▸ unique) trace)

/-- A real accepted literal already supplies the atomic source shape. Unit
uses the empty tuple rule; no nonempty tuple becomes an atomic literal. -/
theorem literal_of_certificate {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id code) :
    LiteralSupported (source := source) (solved := solved) id code := by
  obtain ⟨node, found, literal, selected⟩ := receipt
  refine ⟨node, found, literal, selected, ?_⟩
  rcases code with ⟨type, expression⟩
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ => rw [form]; exact .integerLiteral _ _
  | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

/-- Unit is the only tuple in the atomic literal family. Pair support remains
an ordered two-child tree, with a separate receipt for each occurrence. -/
theorem literal_tuple_empty {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (supported : LiteralSupported (source := source) (solved := solved) id code)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {items : List ExpressionId} (form : node.form = .tuple items) : items = [] := by
  obtain ⟨other, actual, _, _, atomic⟩ := supported
  have same := Option.some.inj (actual.symm.trans found)
  subst other
  rw [form] at atomic
  cases atomic
  rfl

/-- The original accepted read plus its independent raw binding is enough for
the first read family; a native payload type never supplies this binding. -/
theorem read_of_accepted {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (accepted : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id code)
    (ordinary : ∀ receipt : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) code.expression,
      receipt.type = code.type → CompatibleExpressionReads.StaticBinding receipt context →
      ¬ ∃ key value, receipt.declared.scheme.body = .mapping key value) :
    ReadSupported (fuel := fuel) (values := values) (source := source) (context := context)
      (reasonAt := reasonAt) (scope := scope) id code := by
  obtain ⟨receipt, type, binding⟩ := accepted
  exact ⟨receipt, type, binding, ordinary receipt type binding⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
/-! A finite staged tuple grammar with concrete primitive leaves. Tuple nodes
retain the actual ordered compiler vector, including repeated occurrences.
The child support is static; the unique structural proof supplies its meanings.
This does not certify the full general expression or callable grammar. -/
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev FaultRep (faults : FunctionCalls.FaultRep) : RecursiveStageMeaning.FaultRep
  | .semantic reason, token => faults reason token
  | .stage _ _ _, _ => False

def Entries (scope : SourceCoreLocalCell.Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

inductive Tree (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | primitive {id code}
      (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code) :
      Tree fuel values source context solved reasonAt scope id code
  | tuple {id node ids types codes entries}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source (Entries scope entries) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ entries → Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments codes)

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope}

inductive Supported : {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id code → Prop where
  | primitive {id code}
      (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code)
      (sites : RecursiveStagePrimitiveMeaning.Supported tree) : Supported (.primitive tree)
  | tuple {id node ids types codes entries}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source (Entries scope entries) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ entries → Tree fuel values source context solved reasonAt scope child code)
      (sites : ∀ child code (member : (child, code) ∈ entries), Supported (children child code member)) :
      Supported (.tuple header sequence children)

def Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ tree : Tree fuel values source context solved reasonAt scope id code, Supported tree


/-- Static primitive leaves keep the original compiler tree and all its sites. -/
def PrimitiveCertificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code,
    RecursiveStagePrimitiveMeaning.Supported tree

/-- A finite tuple tree over concrete static leaf receipts. Only the reached
ordered mapM children occur; repeated identifiers and all leaf metadata remain. -/
inductive TreeFor (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (leaves : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | leaf {id code} (receipt : leaves scope id code) : TreeFor values source leaves scope id code
  | tuple {id node ids types codes entries}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source (Entries scope entries) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ entries → TreeFor values source leaves scope child code) :
      TreeFor values source leaves scope id (SourceCoreCalls.packArguments codes)

def CertificateFor (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (leaves : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id code => TreeFor values source leaves scope id code

/-- The original primitive grammar enters the same tuple proof by retaining
its actual supported tree, rather than reconstructing a leaf from an outcome. -/
theorem Supported.toFor {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (sites : Supported tree) :
    TreeFor values source (PrimitiveCertificate fuel values source context solved reasonAt) scope id code := by
  induction sites with
  | primitive tree supported => exact .leaf ⟨tree, supported⟩
  | tuple header sequence children sites ih => exact .tuple header sequence ih

inductive PacksOutcome : Staging.Recursive.ValuesOutcome → Staging.Recursive.Outcome → Prop where
  | values {values value} (pack : Dynamic.ValuesPack values value) : PacksOutcome (.values values) (.value value)
  | fault (failure) : PacksOutcome (.fault failure) (.fault failure)

theorem PacksOutcome.functional {sequence : Staging.Recursive.ValuesOutcome} {left right : Staging.Recursive.Outcome}
    (first : PacksOutcome sequence left) (second : PacksOutcome sequence right) : left = right := by
  cases first with
  | values pack => cases second with | values other => exact congrArg _ (pack.functional other)
  | fault => cases second; rfl

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Both the new arbitrary-length rules and the retained unit/pair rules expose
one ordered staged list. No source trace is recovered from a native result. -/
theorem source_inv {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    {ids : List ExpressionId} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ sequence, Staging.Recursive.Expressions program stages invocation context environment before ids sequence after ∧
      PacksOutcome sequence outcome := by
  cases trace with
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
    cases same
    rw [form] at localForm
    cases localForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic uncoerced raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
    subst node
    rw [form] at atomic raw
    cases atomic
    cases raw with
    | tuple _ children pack =>
      cases children
      cases pack
      exact ⟨_, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
    subst node
    rw [form] at atomic raw
    cases atomic
    cases raw with | tuple _ children => cases children
  | pair owned first second =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .cons first (.cons second .nil), .values (.cons (.singleton _))⟩
  | pairLeftFault owned child =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .headFault child, .fault _⟩
  | pairRightFault owned first failed =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, .tailFault first (.headFault failed), .fault _⟩
  | tupleValue owned children pack =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, children, .values pack⟩
  | tupleFault owned children =>
    have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
    subst ids
    exact ⟨_, children, .fault _⟩
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorValue owned _ _ | constructorFault owned _ =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | group owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unary owned child applied =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _ =>
    have same := occurrence_form unique metadata.found owned
    rw [form] at same
    cases same
  | unaryOperandFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | unaryInvalid owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryLeftFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryLeftInvalid owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryShortCircuit owned child circuit =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryRightFault owned first continues child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binary owned first continues second applies =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | binaryInvalid owned first continues second invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | conditional owned test branch =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | conditionalFault owned test =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | calleeFault owned child =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | notCallable owned child invalid =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | rejected owned child rejected =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | argumentsFault owned child guard children =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | sourceArity owned child guard children mismatch =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible
  | applied owned uncoerced child guard children arity applied =>
    have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
    cases impossible

/-- The independent tuple occurrence consumes the very same staged list. -/
theorem source_intro {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {id : ExpressionId} {ids : List ExpressionId} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {sequence : Staging.Recursive.ValuesOutcome} {outcome : Staging.Recursive.Outcome}
    (owned : Staging.Recursive.Occurrence invocation id (.tuple ids))
    (children : Staging.Recursive.Expressions program stages invocation context environment before ids sequence after)
    (packed : PacksOutcome sequence outcome) :
    Staging.Recursive.Expression program stages invocation context environment before id outcome after := by
  cases packed with
  | values pack => exact .tupleValue owned children pack
  | fault => exact .tupleFault owned children


theorem sequence_result {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {faults : RecursiveStageMeaning.FaultRep} {sequence : Staging.Recursive.ValuesOutcome} {value : Value}
    (represented : RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world types codes faults sequence value) :
    ∃ outcome, PacksOutcome sequence outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (TypeSystem.Ty.productMany types) (SourceCoreCalls.packArguments codes).type faults outcome value := by
  cases represented with
  | values related =>
    obtain ⟨packed, pack, payload⟩ := CompatibleExpressionTuples.values_pack related
    exact ⟨_, .values pack, .value (by simpa only [CompatibleExpressionConstructorNativeTyping.packed_type,
      CompatibleAmbientHeap.payloadModel] using payload)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩

section TupleStep
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

private theorem tuple_reflects
    (meaning : RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context children faults) :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CompatibleExpressionTuples.Certificate values invocation.source children) faults := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  intro root found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have same := Option.some.inj (header.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStageArguments.reflects_for sequence meaning environments heaps locals agrees evaluated
  obtain ⟨outcome, packed, payload⟩ := sequence_result represented
  have owned : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨node, lookupExpression?_sound header.metadata.found, header.form, header.metadata.requirements, header.metadata.coercions⟩
  exact ⟨outcome, after, finalMap, finalWorld, source_intro owned sourceTrace packed,
    by simpa only [header.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata⟩

private theorem tuple_preserves (unique : NodeOccurrencesUnique invocation.source)
    (meaning : RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context children faults) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CompatibleExpressionTuples.Certificate values invocation.source children) faults := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  intro root found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  have same := Option.some.inj (header.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, sourceTrace, sourcePacked⟩ := source_inv header.metadata header.form unique trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStageArguments.preserves_for sequence meaning environments heaps locals agrees sourceTrace
  obtain ⟨result, packed, payload⟩ := sequence_result represented
  have same := sourcePacked.functional packed
  subst result
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
    by simpa only [header.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata⟩
end TupleStep


section WithLeaves
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  {leaves : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- The sole ordered tuple reflection consumes each original native child.
Concrete upper families discharge the static leaf meanings internally. -/
theorem reflects_with_leaves
    (meaning : RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context leaves faults) :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CertificateFor values invocation.source leaves) faults := by
  intro scope id code tree
  induction tree with
  | leaf receipt => exact meaning receipt
  | tuple header sequence children ih =>
    intro node found mapping world admin environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    refine tuple_reflects functions program stages invocation ?_ ⟨_, _, _, _, rfl, header, sequence⟩
      found environments heaps locals agrees evaluated
    intro current child childCode certified
    obtain ⟨rfl, member⟩ := certified
    exact ih child childCode member

/-- The same ordered tuple proof preserves successful leaves and the first
failure. Its leaf laws use the same full heap and metadata relation. -/
theorem preserves_with_leaves (unique : NodeOccurrencesUnique invocation.source)
    (meaning : RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context leaves faults) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (CertificateFor values invocation.source leaves) faults := by
  intro scope id code tree
  induction tree with
  | leaf receipt => exact meaning receipt
  | tuple header sequence children ih =>
    intro node found mapping world admin environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    refine tuple_preserves functions program stages invocation unique ?_ ⟨_, _, _, _, rfl, header, sequence⟩
      found environments heaps locals agrees trace
    intro current child childCode certified
    obtain ⟨rfl, member⟩ := certified
    exact ih child childCode member
end WithLeaves

section Meaning
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger runtime uninitialized in
/-- Each original native child is reflected by the same finite supported tree.
No preceding source trace or preservation theorem enters this direction. -/
theorem reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt) (FaultRep faults) := by
  cases sameSource
  intro scope id code certified
  obtain ⟨tree, supported⟩ := certified
  refine reflects_with_leaves functions program stages invocation ?_ supported.toFor
  intro current child childCode leaf
  obtain ⟨tree, sites⟩ := leaf
  intro node found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.reflects functions program stages invocation rfl uninitialized sameLedger runtime
      sites found environments heaps locals agrees evaluated
  refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

include sameSource sameLedger runtime uninitialized in
/-- Preservation uses the sole ordered pack proof at each tuple node. The
primitive theorem discharges its own stage-fault impossibility. -/
theorem preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt) (FaultRep faults) := by
  cases sameSource
  intro scope id code certified
  obtain ⟨tree, supported⟩ := certified
  refine preserves_with_leaves functions program stages invocation unique ?_ supported.toFor
  intro current child childCode leaf
  obtain ⟨tree, sites⟩ := leaf
  intro node found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.preserves functions program stages invocation rfl unique uninitialized
      extension sameLedger runtime sites found environments heaps locals agrees trace
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

end Meaning


section Extraction
/-- A real literal receipt keeps the complete selected numeric row. -/
theorem literal {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id code) :
    Certificate fuel values source context solved reasonAt scope id code :=
  ⟨.primitive (.product (.literal receipt.forget)), .primitive _
    (.product _ (.literal receipt.forget (RecursiveStagePrimitiveMeaning.literal_of_certificate receipt)))⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This fold transports only actual child receipts and raw source types. -/
private theorem child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {budget : Nat}
    {compilation : SourceCoreFunctions.Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

/-- The actual ordered child vector is certified once for every concrete leaf family. -/
private theorem of_ordered_children (leaves : GenericExpressionMeaning.Certificate)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type)
    (acceptedChildren : ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope child reasonAt) = .ok codes)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      CertificateFor values source leaves scope child code) :
    CertificateFor values source leaves scope id (SourceCoreCalls.packArguments codes) := by
  obtain ⟨types, typedChildren, sourceType⟩ := CompatibleExpressionTuples.source_types unique found form metadata.coercions typed
  obtain ⟨count, nodes, children⟩ := child_certificates unique typedChildren acceptedChildren extract
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (certificate := Entries scope (ids.zip codes)) count nodes (fun child code member => ⟨rfl, member⟩)
  exact .tuple ⟨metadata, form, sourceType⟩ sequence children

/-- The legacy static receipt is an erasure of the same finite tuple tree.
Only primitive leaves are accepted by this conversion. -/
theorem TreeFor.toOriginal {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (tree : TreeFor values source (PrimitiveCertificate fuel values source context solved reasonAt) scope id code) :
    Certificate fuel values source context solved reasonAt scope id code := by
  classical
  induction tree with
  | leaf receipt =>
    obtain ⟨tree, sites⟩ := receipt
    exact ⟨.primitive tree, .primitive tree sites⟩
  | tuple header sequence children ih =>
    let trees := fun child code member => (ih child code member).choose
    have sites := fun child code member => (ih child code member).choose_spec
    exact ⟨.tuple header sequence trees, .tuple header sequence trees sites⟩

/-- The production tuple branch returns its exact mapM child vector. The caller
must discharge each reached child's static certificate from that child's actual
acceptance; this theorem does not automate the full general expression grammar. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok lowered)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      Certificate fuel values source context compilation.solvedRequirements reasonAt scope child code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  obtain ⟨codes, acceptedChildren, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
    found form special readPolicy leaf accepted
  have built := of_ordered_children
    (PrimitiveCertificate fuel values source context compilation.solvedRequirements reasonAt)
    unique found form typed metadata acceptedChildren
    (fun child member childNode code childFound childTyped childAccepted =>
      (extract child member childNode code childFound childTyped childAccepted).choose_spec.toFor)
  exact built.toOriginal


/-- The production tuple branch returns its exact mapM child vector. The caller
must discharge each reached child's static certificate from that child's actual
acceptance; this theorem does not automate the full general expression grammar. -/
theorem of_functions_with_leaves (leaves : GenericExpressionMeaning.Certificate) {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok lowered)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      CertificateFor values source leaves scope child code) :
    CertificateFor values source leaves scope id lowered := by
  obtain ⟨codes, acceptedChildren, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
    found form special readPolicy leaf accepted
  exact of_ordered_children leaves unique found form typed metadata acceptedChildren extract

end Extraction

end Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
/-! Staged mapping reads reconstruct their source initialization from the
original completed Core derivation. The static encoder receipt authenticates
its empty mapping, and the actual native write retains the entire heap. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

/-- Pure quoted values are recovered by inspecting their original execution.
No second execution or determinism argument is used. -/
theorem quoted_completed {native result : Value} {code : Expr}
    (quoted : Quoted native code) {environment : Environment} {before after : Store}
    (evaluated : Evaluates environment before code result after) : result = native ∧ after = before := by
  exact CompatibleExpressionReadCompletion.quoted_completed quoted evaluated

private theorem var_completed {environment : Environment} {before after : Store}
    {index : Nat} {expected result : Value}
    (lookup : environment[index]? = some expected)
    (evaluated : Evaluates environment before (.var index) result after) : result = expected ∧ after = before := by
  exact CompatibleExpressionReadCompletion.var_completed lookup evaluated

private theorem load_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {result : Value}
    (lookup : environment[index]? = some (.cellRef type target))
    (evaluated : Evaluates environment before (.loadCell (.var index)) result after) :
    before.read? target = some result ∧ after = before := by
  exact CompatibleExpressionReadCompletion.load_completed lookup evaluated

/-- The original lazy-read code either keeps its present payload or writes the
quoted empty value to that same cell. The original write determines the final
store, including all unrelated and administrative cells. -/
theorem read_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {optional empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef type target))
    (read : before.read? target = some optional) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ result = .inRight .word payload ∧ after = before) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ result = .inRight .word empty ∧
      before.write? target (.inRight .unit empty) = some after) := by
  exact CompatibleExpressionReadCompletion.read_completed lookup read quoted evaluated


variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- This leaf retains the actual local-read compiler receipt and its independent
raw source binding. Only declared mappings enter this separate family. -/
def Supported : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ receipt : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) lowered.expression,
    receipt.type = lowered.type ∧ CompatibleExpressionReads.StaticBinding receipt context ∧
    ∃ key value, receipt.declared.scheme.body = .mapping key value

/-- The real compiler and an independently typed, reached mapping declaration
supply the leaf certificate. Coincident native projections do not select it. -/
theorem of_accepted {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {declared : TypedBinder} {key value : TypeSystem.Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (typed : ExpressionHasType source context id node.type)
    (form : node.form = .reference name (.local binder))
    (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
    (declaredType : declared.scheme.body = .mapping key value) :
    Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt) scope id lowered := by
  obtain ⟨certificate, sameType, binding⟩ :=
    CompatibleExpressionReads.loweredRead_of_accepted accepted read unique declarations typed
  have actual := CompatibleExpressionReads.metadata_of_read read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans actual.found)
  have formed := certificate.form
  rw [nodeEq, form] at formed
  have ⟨_, sameBinder⟩ : name = certificate.name ∧ binder = certificate.binder := by
    simpa only [ExpressionForm.reference.injEq, ReferenceResolution.local.injEq] using formed
  have actualDeclaration := certificate.declaration
  rw [← sameBinder] at actualDeclaration
  have sameDeclaration := Except.ok.inj (actualDeclaration.symm.trans declaration)
  refine ⟨certificate, sameType, binding, key, value, ?_⟩
  rw [sameDeclaration]
  exact declaredType

private theorem quoted_rename {native : Value} {literal : Expr} (quoted : Quoted native literal) (ξ : Renaming) :
    literal.rename ξ = literal := by
  exact CompatibleExpressionReadCompletion.quoted_rename quoted ξ

private theorem mapping_rename {native : Value} {literal : Expr} (quoted : Quoted native literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  exact CompatibleExpressionReadCompletion.mapping_rename quoted index ξ

private theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  exact CompatibleExpressionReadCompletion.cells_write_exists found value

private theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  exact CompatibleExpressionReadCompletion.writes_exists read value


variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : FunctionCalls.FaultRep}

include sameSource extension in
/-- The original completed mapping read supplies either the stored source value
or the actual empty-mapping write. Reflection never invokes preservation,
constructs a native replay, or uses evaluation determinism. -/
theorem reflects :
    RecursiveStagePrimitiveMeaning.Reflects functions (registry := registry) program stages invocation context
      (Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt)) faults := by
  intro scope id lowered supported root found mapping world administrative environment canonical actual before store ξ result finalStore
    environments heaps locals agrees evaluated
  obtain ⟨certificate, sameType, binding, declaredMapping⟩ := supported
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (sameSource ▸ found))
  obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata⟩ :=
    certificate.mapping_completed (faults := faults) functions extension program context invocation.evidence binding declaredMapping
      environments heaps locals agrees evaluated
  have contains : ContainsExpression invocation.source id certificate.node := by
    simpa only [sameSource] using lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := certificate.form ▸ .reference _ _
  cases represented with
  | value payload =>
    refine ⟨.value sourceValue, after, mapping, world,
      .atomicValue contains atomic certificate.metadata.coercions ?_, .value ?_,
      finalHeaps, .refl _, .refl _, frame, metadata⟩
    · simpa only [sameSource, certificate.metadata.requirements] using raw
    · simpa only [CompatibleAmbientHeap.payloadModel, nodeEq, sameType] using payload

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

private theorem reference_no_stage {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    {program : Program} {stages : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {failedScope : Staging.Recursive.Scope} {call : ExpressionId} {reason : Staging.CallGuard.Fault}
    (trace : Staging.Recursive.Expression program stages invocation context environment before id
      (.fault (.stage failedScope call reason)) after) : False := by
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [coercions] at path
      cases path
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorFault owned children | tupleFault owned children =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | group owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | pairLeftFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | pairRightFault owned first second =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _ =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | unaryOperandFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | binaryLeftFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | binaryRightFault owned first continues second =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | conditional owned test branch =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | conditionalFault owned test =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | calleeFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | rejected owned child guard =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | argumentsFault owned child guard children =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | applied owned uncoerced child guard children arity applies =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same

include sameSource extension in
/-- Forward mapping-read preservation reuses the ordinary read proof and the
independent staged erasure. A local reference cannot conceal a stage rejection. -/
theorem preserves (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (supported : Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt) scope id code)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨certificate, sameType, binding, _⟩ := supported
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (sameSource ▸ found))
  have plain := fun (outcome : Dynamic.ExpressionOutcome)
      (evaluation : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence source environment before id outcome after) =>
    certificate.preserves functions extension program context invocation.evidence binding environments heaps locals agrees
      (uninitialized id) unique evaluation
  cases outcome with
  | value output =>
    obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
      plain _ (.value (sameSource ▸ trace.value_plain))
    cases represented with
    | value payload =>
      refine ⟨_, finalStore, mapping, world, evaluated, .value ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
      simpa only [CompatibleAmbientHeap.payloadModel, nodeEq, sameType] using payload
  | fault failure =>
    cases failure with
    | semantic reason =>
      obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
        plain _ (.fault (sameSource ▸ trace.semanticFault_plain))
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, mapping, world, evaluated, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
        simpa only [sameType] using (RecursiveStagePrimitiveMeaning.Result.fault (functions := functions) (registry := registry) matched)
    | stage failedScope call reason =>
      exact False.elim (reference_no_stage (sameSource ▸ unique) found (nodeEq ▸ certificate.form) (nodeEq ▸ certificate.metadata.coercions) trace)

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
/-! Concrete staged tuples may contain ordinary supported primitive leaves or
actual mapping reads. The common ordered tuple proof closes the leaf meanings
internally, including lazy initialization and the first failure. Arbitrary
callable expressions and generalized cells remain independent families. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}

/-- Both alternatives retain their actual compiler receipts and source binding. -/
def Leaves (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  RecursiveStageTupleMeaning.PrimitiveCertificate fuel values source context solved reasonAt scope id code ∨
    RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope id code

def Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate :=
  RecursiveStageTupleMeaning.CertificateFor values source (Leaves fuel values source context solved reasonAt)

/-- A mapping leaf enters the finite tree from its exact static read receipt. -/
theorem mapping {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope id code) :
    Certificate fuel values source context solved reasonAt scope id code := .leaf (.inr receipt)

/-- The original primitive family preserves its whole static tree. -/
theorem primitive {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : RecursiveStageTupleMeaning.PrimitiveCertificate fuel values source context solved reasonAt scope id code) :
    Certificate fuel values source context solved reasonAt scope id code := .leaf (.inl receipt)

section Meaning
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger extension runtime uninitialized in
private theorem leaf_reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Leaves fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  intro scope id code receipt
  intro node found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have result : ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld
        node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    rcases receipt with ordinary | selected
    · obtain ⟨tree, sites⟩ := ordinary
      exact RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized
        sameLedger runtime sites found environments heaps locals agrees evaluated
    · exact RecursiveStageMappingReadMeaning.reflects functions program stages invocation sameSource extension
        selected found environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := result
  refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

include sameSource sameLedger extension runtime uninitialized in
private theorem leaf_preserves (unique : NodeOccurrencesUnique source) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Leaves fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  intro scope id code receipt
  intro node found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  have result : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld
        node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    rcases receipt with ordinary | selected
    · obtain ⟨tree, sites⟩ := ordinary
      exact RecursiveStagePrimitiveMeaning.preserves functions program stages invocation sameSource unique uninitialized
        extension sameLedger runtime sites found environments heaps locals agrees trace
    · exact RecursiveStageMappingReadMeaning.preserves functions program stages invocation sameSource extension unique
        uninitialized selected found environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ := result
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

include sameSource sameLedger extension runtime uninitialized in
/-- Reflection starts with the original ordered Core pack. Each reached read
retains its own raw type and initializes the same cell at the same position. -/
theorem reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  cases sameSource
  exact RecursiveStageTupleMeaning.reflects_with_leaves functions program stages invocation
    (leaf_reflects functions program stages invocation rfl sameLedger extension runtime uninitialized)

include sameSource sameLedger extension runtime uninitialized in
/-- Preservation closes the concrete leaf laws inside the common tuple proof.
No external execution law or preceding native completion is an input. -/
theorem preserves (unique : NodeOccurrencesUnique source) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  cases sameSource
  exact RecursiveStageTupleMeaning.preserves_with_leaves functions program stages invocation unique
    (leaf_preserves functions program stages invocation rfl sameLedger extension runtime uninitialized unique)
end Meaning

/-- The actual function lowerer supplies the original ordered child vector.
Only static receipts from the reached child acceptances are required. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok lowered)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      Certificate fuel values source context compilation.solvedRequirements reasonAt scope child code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id lowered :=
  RecursiveStageTupleMeaning.of_functions_with_leaves
    (Leaves fuel values source context compilation.solvedRequirements reasonAt)
    unique found form typed special readPolicy leaf accepted extract

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
end
