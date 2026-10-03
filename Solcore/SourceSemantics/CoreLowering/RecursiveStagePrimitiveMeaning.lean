import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime

/-! Direct staged primitive correspondence over the actual compatible ambient
heap. Static support retains the original compiler tree and selected literal
rows. Empty tuples and mapping lazy initialization are outside this first
support family. Methods, coercions and callable bodies remain separate. -/
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
  | word strict | integer strict => cases circuit <;> cases strict
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
  | word strict | integer strict => cases strict <;> exact bind_failed child evaluated
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
  | atomic {id node} (found : source.lookupExpression? id = some node)
      (shape : Staging.Recursive.AtomicForm node.form) : CallFree source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : CallFree source inner) : CallFree source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right]) (first : CallFree source left) (second : CallFree source right) : CallFree source id
  | unary {id node operator operand} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : CallFree source operand) : CallFree source id
  | binary {id node left operator right} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right) (first : CallFree source left) (second : CallFree source right) : CallFree source id

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form) : node.form = form := by
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
  | atomic found atomic =>
    cases trace with
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
  | group found form child ih =>
    cases trace with
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
  | pair found form first second firstIH secondIH =>
    cases trace with
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
  | unary found form child ih =>
    cases trace with
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
  | binary found form first second firstIH secondIH =>
    cases trace with
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
  | literal receipt leaf => obtain ⟨node, found, _, _, atomic⟩ := leaf; exact .atomic found atomic
  | read receipt ordinary =>
    obtain ⟨certificate, _, _, _⟩ := ordinary
    exact .atomic certificate.metadata.found (certificate.form ▸ .reference _ _)
  | group metadata form _ _ _ _ ih => exact .group metadata.found form ih
  | pair metadata form _ _ _ _ _ _ _ firstIH secondIH => exact .pair metadata.found form firstIH secondIH

private theorem Supported.callFree {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {tree : Tree fuel values source context solved reasonAt scope id code} (supported : Supported tree) : CallFree source id := by
  induction supported with
  | product _ sites => exact sites.callFree
  | group metadata form _ _ _ _ ih => exact .group metadata.found form ih
  | pair metadata form _ _ _ _ _ _ _ firstIH secondIH => exact .pair metadata.found form firstIH secondIH
  | unary metadata form _ _ _ _ _ _ ih => exact .unary metadata.found form ih
  | binary metadata form _ _ _ _ _ _ _ _ _ _ firstIH secondIH => exact .binary metadata.found form firstIH secondIH

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

/-- Supported leaves retain every selected row; the unit literal is a separate
source-rule gap rather than an ordinary-ledger assumption. -/
theorem literal_no_unit {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (supported : LiteralSupported (source := source) (solved := solved) id code)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) : node.form ≠ .tuple [] := by
  obtain ⟨other, actual, _, _, atomic⟩ := supported
  have same := Option.some.inj (actual.symm.trans found)
  subst other
  intro form
  rw [form] at atomic
  cases atomic

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
