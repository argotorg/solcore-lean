import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions

/-!
# Selected compilations: method and mixed roots

Root support and bounds of methods and mixed roots: invocation bounds, argument rows and physical captures.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedArgumentsReceiving
/-! A returned callable can occur repeatedly in arbitrary ordered arguments
and nested carriers. Its prior semantic result supplies Source meaning and
typing; actual startup fixes every native payload and intermediate metadata.
The complete lists retain the current mapping, world and Source heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedArgumentsReceiving
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicReturnedInputs (Inputs)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedParameterCertificates (Binding)

private theorem projected_at {checked : SourceCoreCompatibleCatalog.Checked}
    {bindings : List Binding} {index : Nat} {binding : Binding}
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (found : bindings[index]? = some binding) :
    checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  induction bindings generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.map_cons] at projected
      obtain ⟨type, types, headProjected, tailProjected, shape⟩ := CompatibleEncoding.project_cons projected
      have parts := List.cons.inj shape
      have headActual : checked.catalog.project head.1.scheme.body = .ok head.2 := by
        simpa only [← parts.1] using headProjected
      have tailActual : (tail.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
          .ok (tail.map Prod.snd) := by
        simpa only [← parts.2] using tailProjected
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact headActual
      | succ index => exact ih tailActual found

/-- Reconstruct both complete lists from their original positions. Exact
lengths exclude silently discarded native or Source suffixes. -/
private theorem arguments_of_positions
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (sourceLength : sources.length = bindings.length) (nativeLength : native.length = bindings.length)
    (positions : ∀ {index : Nat} {binding : Binding}, bindings[index]? = some binding →
      ∃ source value, sources[index]? = some source ∧ native[index]? = some value ∧
        ValueRep checked registry functions mapping world binding.1.scheme.body source value binding.2 ∧
        Dynamic.ValueHasType context heap source binding.1.scheme.body) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources native ∧
      Dynamic.ValuesHaveTypes context heap sources (bindings.map (fun binding => binding.1.scheme.body)) := by
  induction bindings generalizing sources native with
  | nil =>
      have sourceNil := List.eq_nil_of_length_eq_zero sourceLength
      have nativeNil := List.eq_nil_of_length_eq_zero nativeLength
      subst sources
      subst native
      exact ⟨.nil, .nil⟩
  | cons binding bindings ih =>
      cases sources with
      | nil => simp at sourceLength
      | cons source sources =>
          cases native with
          | nil => simp at nativeLength
          | cons value native =>
              obtain ⟨actualSource, actualValue, sourceAt, valueAt, represented, typed⟩ :=
                positions (index := 0) rfl
              have sameSource : source = actualSource := Option.some.inj sourceAt
              have sameValue : value = actualValue := Option.some.inj valueAt
              subst actualSource
              subst actualValue
              simp only [List.length_cons] at sourceLength nativeLength
              have remaining := ih (Nat.succ.inj sourceLength) (Nat.succ.inj nativeLength) (by
                intro index next found
                exact positions (index := index + 1) found)
              exact ⟨.cons represented remaining.1, .cons typed remaining.2⟩

/-- The previous represented result and this original input encoding produce
all current arguments, including repeated and nested copies of the exported
handle. Registry extensions preserve both prior and newly encoded metadata. -/
theorem StartAt.returned_arguments_receiving
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel returnedFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments inputFuel checkpoint recipe root world store native encodedValues)
    (functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
    {returnedType : TypeSystem.Ty} {returnedValue : SourceCorePublicValues.Value}
    {returnedSource : Dynamic.Value} {returnedNative : Core.Value} {returnedNativeType : Core.Ty}
    (imported : session.EncodesAt returnedFuel returnedType returnedValue returnedNative)
    {handle : Handle} (handleValue : returnedValue = .function handle)
    {prior receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {heap : Dynamic.Heap}
    (priorRep : ValueRep recipe.compiled.compatible.checked prior functions mapping world
      returnedType returnedSource returnedNative returnedNativeType)
    (priorMetadata : SourceCoreRawMetadata.Extends prior receiving)
    (priorTyped : Dynamic.ValueHasType header.function.context heap returnedSource returnedType)
    {sources : List Dynamic.Value}
    (receipts : Inputs returnedType returnedValue returnedSource header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments sources)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving functions)
      mapping world header.bindings sources native ∧
    Dynamic.ValuesHaveTypes header.function.context heap sources header.types := by
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : sources.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have atReceiving := priorRep.extend priorMetadata (.refl _) (.refl _)
  have assembled := arguments_of_positions (functions := functions) (registry := receiving)
      (mapping := mapping) (world := world) (context := header.function.context) (heap := heap)
      sourceCount nativeCount (by
        intro index binding bindingAt
        have rawAt : (header.bindings.map (fun binding => binding.1.scheme.body))[index]? =
            some binding.1.scheme.body := by
          simp only [List.getElem?_map, bindingAt, Option.map_some]
        obtain ⟨publicValue, source, publicAt, sourceAt, receipt⟩ := receipts.lookup rawAt
        have bindingProjected := projected_at projected bindingAt
        have rawRoot : root.inputs[index]? = some binding.1.scheme.body := by
          rw [rawInputs]
          exact rawAt
        obtain ⟨before, encoded, type, valueAt, typeAt, projection, owner, accepted, extended⟩ :=
          RecursiveNamedPublicNestedRawInputs.StartAt.raw_input started rawRoot publicAt
        obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
        have sameValue : actual = encoded.value := Option.some.inj (actualAt.symm.trans valueAt)
        subst actual
        obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicReturnedEncoding.Input.meaning
          receipt started.recipe_eq imported handleValue atReceiving priorTyped
        have represented := meaning owner rfl accepted projection typed (extended.trans metadata)
        have typeEq := Except.ok.inj (projection.symm.trans bindingProjected)
        exact ⟨source, encoded.value, sourceAt, valueAt, typeEq ▸ represented, sourceTyped⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedArgumentsReceiving
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
/-! Static roots for expressions whose ordinary and trait calls use the actual
physical cache. Ports retain source selection and compilation evidence; the
numeric proof supplies every called-body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open SelectedCompilationRootStaticSupport (RootData)

/-- This first physical method family covers statically selected call sites. -/
def NoIndirect {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered) : Prop :=
  ∀ {fuel callScope callId callee ids metadata callCode}
    (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
      invocation.source callScope callId callee ids metadata reasonAt callCode),
    Calls compiler root → False

structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    DirectCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
      compiler headers context invocation.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header }
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate
  methodReady : ∀ {fuel callScope callId callCode}
    (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId reasonAt callCode),
    MethodCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port
      (compiled := compiled) compiler context invocation.evidence stages //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
        port.principal.traitName port.principal.methodName compiler.node.requirements
        port.principal.sourceBody port.principal.dictionary }
  noIndirect : NoIndirect (compiled := compiled) (invocation := invocation) toRootData.certificate

structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : Root compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

def RootAt.ofRoot
    (root : Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

/-- Original syntax can exclude indirect calls independently of compiler certificates. -/
def NoIndirectSource (source : TypedSource) : Prop :=
  ∀ id node callee ids metadata, source.lookupExpression? id = some node →
    node.form = .call callee ids (.indirect metadata) → False

theorem NoIndirect.of_source
    (root : Certificate policy lowerBody compilation readFuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope expression lowered)
    (syntaxOnly : NoIndirectSource invocation.source) :
    NoIndirect (compiled := compiled) (invocation := invocation) root := by
  intro fuel callScope callId callee ids metadata callCode compiler _path
  exact syntaxOnly callId compiler.original callee ids metadata compiler.found compiler.originalForm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
/-! Static terminal method packets retain the genuine trait principal, exact
parameter context and original accepted body. The selected instance certificate and
the actual compiler callback provide the used child; no execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallablePreparedMethodRuntimeProfileFactory (SourceAt policy scope)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

def Certified (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary) : Prop :=
  ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    principal.sourceBody sourceAt.types sourceAt.context facts

/-- The actual selector contributes only its own retained method certificate. -/
theorem Certified.of_typed
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller traitName methodName requirements principal.sourceBody principal.dictionary) :
    Certified principal sourceAt := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ certificate =>
    obtain ⟨types, lexical, facts, typed⟩ := certificate
    have contextEq := Dynamic.MonoBindersExtend.functional typed.typing.inputs_extend sourceAt.extended
    have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq typed.typing.inputs_extend).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq sourceAt.extended)
    exact ⟨facts, typesEq ▸ contextEq ▸ typed.toBodyInstanceTypingCertificate⟩

structure Packet where
  sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary
  expression : ExpressionId
  receipt : Receipt (policy principal.cached.compilation) compiled.indexed.fuel principal.sourceBody.source
    (scope (named := principal.named)) expression principal.cached.compilation.statements
    principal.named.signature.resultType (principal.cached.diagnostics.reasonAt principal.named.signature.key)
    principal.cached.compilation.own.fellThroughReason principal.cached.compilation.own.table.escapedReason
    principal.cached.compilation.body

/-- The actual selected Source method determines typing in the same parameter
context retained by SourceAt; native type projection is not used for this step. -/
theorem source_typing (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
    principal.sourceBody principal.dictionary)
    (certified : Certified principal sourceAt) :
    ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      principal.sourceBody sourceAt.types sourceAt.context facts := by
  exact certified

theorem statements (packet : Packet principal)
    (certified : Certified principal packet.sourceAt) :
    ∃ final facts, StatementsHaveType principal.sourceBody.source {returnType := principal.sourceBody.resultType}
      packet.sourceAt.context principal.cached.compilation.statements final facts ∧
      BodyCompletes principal.sourceBody.resultType facts := by
  obtain ⟨facts, typed⟩ := source_typing principal packet.sourceAt certified
  obtain ⟨final, body, _roots, complete⟩ := typed.typing.body_typed
  refine ⟨final, facts, ?_, complete⟩
  have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
    principal.source_frame.roots.filterMap_eq
  exact roots ▸ body

/-- Original Source typing selects the actual terminal expression and raw result. -/
theorem child_typed (packet : Packet principal)
    (certified : Certified principal packet.sourceAt)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    ∃ node, child.source.lookupExpression? packet.expression = some node ∧
      node.type = principal.sourceBody.resultType ∧
      ExpressionHasType child.source packet.sourceAt.context packet.expression node.type := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨final, facts, typed, complete⟩ := statements principal packet certified
  rw [← sourceEq] at typed
  exact CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed
    (sourceEq ▸ packet.sourceAt.unique) (packet.receipt.head child sourceEq) typed complete

/-- Static validity is transported along the genuine method parameter extension. -/
theorem runtime (packet : Packet principal)
    (certified : Certified principal packet.sourceAt) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      packet.sourceAt.context principal.sourceBody.source := by
  obtain ⟨_facts, typed⟩ := source_typing principal packet.sourceAt certified
  exact typed.sourceRuntimeValid.transport (RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended)

/-- The exact contextual compiler action selects one shared policy for the
method child, preserving the actual specializer row and callback budget. -/
theorem policy_receipt (packet : Packet principal) :
    ∃ fuel, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      fuel principal.sourceBody.source (scope (named := principal.named)) packet.expression
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) packet.receipt.child) := by
  have accepted := packet.receipt.generated
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none packet.receipt.childFuel principal.sourceBody.source
    (scope (named := principal.named)) packet.expression
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok packet.receipt.child at accepted
  cases eq : packet.receipt.childFuel with
  | zero =>
    rw [eq, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases accepted
  | succ fuel =>
    exact ⟨fuel, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record (by simpa only [eq] using accepted)⟩

/-- Only the actual original terminal syntax is needed in addition to SourceAt. -/
theorem of_terminal
    (sourceAt : SourceAt principal.cached.compilation (.initial compiled.compatible.checked)
      principal.sourceBody principal.dictionary)
    (expression : ExpressionId)
    (terminal : Terminal principal.sourceBody.source expression principal.cached.compilation.statements) :
    Nonempty (Packet principal) := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  exact ⟨⟨sourceAt, expression, receipt⟩⟩

/-- The selected root keeps the method result, diagnostic issuer and real
single packed-argument prefix. Called-body meaning is supplied by the numeric IH. -/
structure Child (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
    (semanticFaults : FunctionCalls.FaultRep) extends
    SelectedCompilationMethodRootSupport.RootAt compiled headers stages
      packet.sourceAt.context child (scope (named := principal.named)) packet.expression
      packet.receipt.child semanticFaults where
  result : rawType = principal.sourceBody.resultType
  reasons : reasonAt = principal.cached.diagnostics.reasonAt principal.named.signature.key
  prefixLength : compilation.administrativePrefix = 1

/-- Every actual selected method scope receives a static expression root. -/
structure Support (packet : Packet principal)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep) : Prop where
  roots : ∀ child, stages.Closure principal.sourceFunction child →
    Nonempty (Child principal packet headers stages child semanticFaults)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
/-! Static roots for expressions whose ordinary and trait calls use the actual
physical cache. Ports retain source selection and compilation evidence; the
numeric proof supplies every called-body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open SelectedCompilationRootStaticSupport (RootData)

structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    DirectCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
      compiler headers context invocation.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header }
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate
  methodReady : ∀ {fuel callScope callId callCode}
    (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId reasonAt callCode),
    MethodCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port
      (compiled := compiled) compiler context invocation.evidence stages //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
        port.principal.traitName port.principal.methodName compiler.node.requirements
        port.principal.sourceBody port.principal.dictionary }

/-- Each conversion retains the genuine terminal method packet at its selected
Source body. Called-body execution is supplied by the shared induction. -/
def CoercionMethods {compiled : SourceCoreUnifiedCompilation.Compiled}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    {stages : Staging.Recursive.Registry} (semanticFaults : FunctionCalls.FaultRep)
    {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
    {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
    {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain
      compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) : Prop :=
  match chain with
  | .nil => True
  | .cons _ port _ tail =>
      (∃ packet : SelectedCompilationMethodBodySupport.Packet port.principal,
        packet.sourceAt = port.sourceAt ∧
        SelectedCompilationMethodBodySupport.Certified port.principal packet.sourceAt ∧
        SelectedCompilationMethodBodySupport.Support
          port.principal packet headers stages semanticFaults) ∧
      CoercionMethods headers semanticFaults tail

/-- The original call, its ordered argument roots and every conversion retain
actual compiler receipts. No source view is sanitized and no body law is stored. -/
structure CoercedDirectRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (resultType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  compilerFuel : Nat
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
    compilation invocation.source scope expression reasonAt = .ok lowered
  project : SourceCoreEvidence.Projector
  caller : SourceSpecialization.SpecializedFunction
  child : SourceCoreEvidence.Child
  fuel : Nat
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller
    compilation child fuel invocation.source scope expression callee arguments instantiation reasonAt
    policy.callables node lowered
  nonempty : node.coercions ≠ []
  result : node.type = resultType
  typed : ExpressionHasType invocation.source context expression node.type
  port : CallableIndexedOwnedPreparedStagedRawDirectAuthority.PortWithEvidence
    actual headers context invocation.evidence
  certified : SelectedCompilationNamedSourceTyping.Certified port.header
  shape : SelectedCompilationSourceSignatureFacts.Shape port.header
  argumentTypes : List TypeSystem.Ty
  argumentCertificate : GenericExpressionMeaning.Certificate
  argumentTree : DataExpressionSequence.Tree invocation.source argumentCertificate
    scope arguments argumentTypes actual.loweredArguments
  argumentRoots : ∀ {current id code}, argumentCertificate current id code →
    ∃ rawType, Nonempty (Root compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt current id code rawType semanticFaults)
  calls : List CallableCoercionSpine.Call
  chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain
    compiled project compilation caller actual.available scope node policy.callables context invocation stages
    node.rawType node.type actual.operand node.coercions lowered calls
  methods : CoercionMethods headers semanticFaults chain
  ledger : context.solvedRequirements = caller.function.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  catalog : SignatureCatalogWellFormed (Program.ofChecked compiled.sourceProgram).signatures
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    context invocation.source
  covers : invocation.evidence.Covers context

/-- Both alternatives retain the same public expression and compiler indices. -/
inductive RootChoice (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  | ordinary : Root compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt scope expression lowered rawType semanticFaults →
      RootChoice compiled headers stages policy lowerBody compilation readFuel
        context invocation reasonAt scope expression lowered rawType semanticFaults
  | coercedDirect : CoercedDirectRoot compiled headers stages policy lowerBody compilation readFuel
      context invocation reasonAt scope expression lowered rawType semanticFaults →
      RootChoice compiled headers stages policy lowerBody compilation readFuel
        context invocation reasonAt scope expression lowered rawType semanticFaults

structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

def RootAt.ofRoot
    (root : Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, .ordinary root⟩

def RootAt.ofChoice
    (root : RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

instance : Coe (Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    (RootChoice compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) := ⟨RootChoice.ordinary⟩

/-- Existing method-only roots retain all their original static receipts. -/
def Root.ofMethod
    (root : SelectedCompilationMethodRootSupport.Root
      compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    Root compiled headers stages policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults :=
  ⟨root.toRootData, root.directReady, root.indexReady, root.methodReady⟩

def RootAt.ofMethod
    (root : SelectedCompilationMethodRootSupport.RootAt
      compiled headers stages context invocation scope expression lowered semanticFaults) :
    RootAt compiled headers stages context invocation scope expression lowered semanticFaults :=
  ⟨root.policy, root.lowerBody, root.compilation, root.readFuel, root.reasonAt, root.rawType,
    .ordinary (Root.ofMethod root.support)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
/-! The numeric family quantifies over roots with actual complete cache state.
Every invocation produces this same carrier through its parameter allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationMixedRootSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
/-! Staged method invocation enters the actual marked parameter prefix and
restores the caller from the body's reached pool. Both callbacks receive the
real complete cache and slot layout, and preserve semantic and stage faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry)
open CallableIndexedOwnedPreparedStagedMethodInvocationEntries

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)


variable {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] installed.canonical)

/-- The Source body callback starts at the exact parameter-produced state. -/
def SourceBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  ∀ {size finalContext bodyOutcome outcome after},
    Staging.Recursive.Size.StatementsIn program stages true size child sourceAt.context entry.environment
      entry.heap generation.statements finalContext bodyOutcome after →
    Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome → size < budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (generation.body.rename entry.embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved sourceBody.context entry.heap after value sourceBody.resultType

/-- Reflection uses the native body's independent strict grade. -/
def NativeBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {prefixSize : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body prefixSize value finalStore)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  entry.childSize < budget →
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context entry.environment
        entry.heap generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), finalMap, finalWorld, after, finalStore, entry.canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved sourceBody.context entry.heap after value sourceBody.resultType

def SourceContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    SourceBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

def NativeContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState) (prefixSize : Nat) (bodyStore : Store)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_prefixWithin : prefixSize < budget)
    {value : Value} {finalStore : Store}
    (_restored : finalStore = bodyStore.set owner.key.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    NativeBodyAt (stages := stages) (child := child) (faults := faults)
      generation sourceAt functions budget entry reached

include sourceAt installed represented sameFrame heaps physical slots in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {bodySize : Nat} {environment : Dynamic.Environment} {bound after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome}
    (allocated : Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters
      arguments environment bound)
    (bodyTrace : Staging.Recursive.Size.StatementsIn program stages true bodySize child sourceAt.context environment
      bound generation.statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome)
    (within : bodySize < budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved sourceBody.context before after value sourceBody.resultType := by
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation sourceAt functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨bodyState, bodyRelated⟩, bodyPreserved⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property bodyTrace matched within
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) read
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned, ?_⟩
  · exact renamed.symm ▸ evaluated
  · intro sourceValue same
    have preserved := bodyPreserved sourceValue same
    exact ⟨preserved.value_typed, preserved.heap_typed, sourceMetadata⟩

include sourceAt installed represented sameFrame heaps physical slots in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults) generation sourceAt functions installed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize environment bound finalContext bodyOutcome outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before (methodFunction generation sourceBody dictionary).parameters arguments environment bound ∧
      Staging.Recursive.Size.StatementsIn program stages true sourceSize child sourceAt.context environment
        bound generation.statements finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult sourceBody.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved sourceBody.context before after value sourceBody.resultType := by
  obtain ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, strict, restored,
    entry, added, length, spine, parameterState, parameterRelated⟩ :=
    body_prefix_with_state generation sourceAt functions installed represented owner caller sameFrame heaps completed
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, bodyTrace, matched, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨bodyState, bodyRelated⟩, bodyPreserved⟩ :=
    bodyMeaning originId index metadata prefixSize bodyStore owned history
      (Nat.lt_of_lt_of_le strict within) restored entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property
      (Nat.lt_of_le_of_lt entry.bounded (Nat.lt_of_lt_of_le strict within))
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position (CallableIndexedAmbient.frame_registered compiled.indexed)
      finalHeaps worlds frame related
  subst finalStore
  exact ⟨sourceSize, entry.environment, entry.heap, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
    entry.allocation, bodyTrace, matched, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned,
    fun sourceValue same => ⟨(bodyPreserved sourceValue same).value_typed,
      (bodyPreserved sourceValue same).heap_typed, sourceMetadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootBounds
/-! The numeric family quantifies over roots with actual complete cache state.
Every invocation produces this same carrier through its parameter allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationMethodRootSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation (Point scope expression lowered) faults size

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
/-! Actual operator typing fixes the raw method argument vector before native
packing. The selected method carries the same result and reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context caller stages)

/-- Empty output coercions identify the complete owned requirement row. -/
theorem requirements : receipt.operator.requirements = receipt.node.requirements := by
  have layout := CallableCallRequirementLayouts.ordinary_owned receipt.operator.ordinary
  simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm

/-- The independent parent judgment supplies the real trait profile and its
ordered operand types. This uses no equality of native packed types. -/
theorem source_facts (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ operand parameterTypes returnTypes predicates,
      ExpressionsHaveTypes source context receipt.arguments parameterTypes ∧
      OperatorProfileInstantiates context port.principal.traitName port.principal.methodName
        operand parameterTypes returnTypes predicates ∧
      RequirementSequenceProves context receipt.node.requirements predicates ∧
      receipt.node.type = TypeSystem.Ty.productMany returnTypes := by
  obtain ⟨selected⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted receipt.operator
  have names : selected.traitName = port.principal.traitName ∧
      selected.methodName = port.principal.methodName := by
    rcases port.dispatch with ⟨operator, operand, form, dispatch⟩ |
      ⟨operator, left, right, form, dispatch⟩
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.unary_dispatch_unique actual dispatch
    · have actual := selected.dispatch
      rw [form] at actual
      exact CallablePreparedOperatorSourceBounds.binary_dispatch_unique actual dispatch
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    CallableIndexedOwnedOperatorSourceAdmission.source_facts selected unique receipt.metadata.coercions typed
  exact ⟨operand, parameterTypes, returnTypes, predicates, children,
    names.1 ▸ names.2 ▸ profile, requirements receipt ▸ proves, result⟩

/-- Full Source typing identifies raw parameters and the result of the same
selected method, including the one-Unit versus no-argument distinction. -/
theorem raw_types
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ExpressionsHaveTypes source context receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, children, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨types ▸ children, bodyResult.trans result.symm⟩

/-- The genuinely reached operand heap is transported to the selected method's
Source context. The full dictionary remains the one retained by the port. -/
theorem at_values
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types ∧
      port.principal.sourceBody.resultType = receipt.node.type := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, _, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq port.sourceAt.extended
  rw [port.sourceAt.parameters, List.map_map] at types
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (types ▸ bodyArguments), bodyResult.trans result.symm⟩

/-- Successful method result typing is returned to the actual caller context. -/
theorem result_at_values
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller
      port.principal.traitName port.principal.methodName receipt.node.requirements
      port.principal.sourceBody port.principal.dictionary)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (preserved : Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after
      value port.principal.sourceBody.resultType) :
    Dynamic.ValueHasType context after value receipt.node.type ∧ Dynamic.HeapWellTyped context after := by
  obtain ⟨operand, parameterTypes, returnTypes, predicates, _children, profile, proves, result⟩ :=
    source_facts receipt port unique typed
  obtain ⟨lexical, facts, certificate, bodyResult⟩ := selected.certificateOfProfile catalog
    runtime.signatures runtime.requirements.idsUnique profile proves
  have signatures := runtime.signatures.trans certificate.signatures_eq.symm
  have resultTyped := preserved.value_typed.transportClosed signatures certificate.type_parameters_empty
    runtime.closed certificate.type_variables_empty runtime.residual_variables_open
  have heapTyped := preserved.heap_typed.transportClosed signatures certificate.type_parameters_empty
    runtime.closed certificate.type_variables_empty runtime.residual_variables_open
  exact ⟨(bodyResult.trans result.symm) ▸ resultTyped, heapTyped⟩

/-- Native bundles are aligned only after the raw row has fixed the arity. -/
theorem represented_arguments
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads := by
  have binderCount : arguments.length = port.principal.named.inputs.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.principal.named.inputs.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.sourceAt.parameterType))
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.principal.named.inputs represented binderCount rfl nativePacked

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
/-! Selected methods recover their authentic installed captures at the reached
heap. Complete physical cache authority supplies native code; the independent
operator selector supplies the method Source frame and dictionary. The current
owner supplies the live frame and full ordered snapshots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open CallableIndexedOwnedPhysicalGlobals

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

open CallableIndexedOwnedMethodPhysicalCaptures (sourceBody Capture)

theorem of_certificate
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {scope : SourceCoreLocalCell.Scope} {caller : Environment} {callerPrefix : Nat}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (pool : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, heap, store, caller⟩)
    (ownerFrame : owner.key.frameLocation = 0)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (slots : Slots compiled callerPrefix scope caller)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (certificate : ∃ types lexical facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (sourceBody (compiled := compiled) (method := method)) types lexical facts)
    :
    Nonempty (Capture cached dictionary functions mapping world heap store caller) := by
  have cachedCode : compiled.indexed.secondPass.closures[cached.index]? = some
      (.lambda cached.named.signature.parameterType (LanguageResult.resultType cached.named.signature.resultType) cached.compilation.output) := by
    simpa only [cached.compilation.emitted] using cached.cached
  obtain ⟨globalUnmapped, globalRead⟩ := physical.cached cachedCode
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed globalRead
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units cached.index capturedTyped
  have captureLayout : EnvironmentsAgree (shift cached.index) (environment compiled)
      (List.replicate cached.index .unit ++ environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[compiled.indexed.base.globals.length]? = _ at frameReference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at frameReference
  let row := pool.rows owner.position
  have frameEq : row.authority.frameLocation = 0 := row.frame_eq.trans ownerFrame
  have frameType := row.authority.typed
  have unmapped := row.authority.unmapped
  have frame := row.authority.frame
  rw [frameEq] at frameType unmapped frame
  obtain ⟨_types, _context, _facts, certified⟩ := certificate
  let installed : Installed cached.compilation (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := sourceBody (compiled := compiled) (method := method))
      (administrative := administrative) functions mapping world heap store caller := {
    canonical := environment compiled
    captured := List.replicate cached.index .unit ++ environment compiled
    capturedContext := capturedContext, embedding := shift cached.index
    environments := .nil canonicalTyped
    locals := by rw [certified.locals_empty]; exact .nil
    captureLayout := captureLayout, captureTyped := capturedTyped
    frameLocation := 0, canonicalReference := frameReference, capturedReference := captureLayout frameReference
    unmapped := unmapped, frameTyped := frameType
    current := row.authority.current, currentGhost := row.authority.ghost, caller := frame
    records := row.authority.records, snapshots := row.authority.snapshots
    globalIndex := scope.length + callerPrefix + cached.index
    globalLocation := location compiled cached.index
    globalUnmapped := globalUnmapped
    globalReference := slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
    globalRead := globalRead }
  exact ⟨⟨administrative, installed, cached.frame selected, rfl, rfl, rfl, rfl⟩⟩

theorem of_typed
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {scope : SourceCoreLocalCell.Scope} {caller : Environment} {callerPrefix : Nat}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (pool : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, heap, store, caller⟩)
    (ownerFrame : owner.key.frameLocation = 0)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (slots : Slots compiled callerPrefix scope caller)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    :
    Nonempty (Capture cached dictionary functions mapping world heap store caller) := by
  apply of_certificate cached dictionary functions owner pool ownerFrame physical typed slots selected.selected
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ certificate =>
    obtain ⟨types, lexical, facts, certified⟩ := certificate
    exact ⟨types, lexical, facts, certified.toBodyInstanceTypingCertificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentBounds
/-! Ordered staged arguments are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

open SelectedCompilationExpressionSequence (PostAdmission)
open CallableIndexedOwnedPreparedStagedMethodArgumentBounds (Trace)

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : Trace budget program registry invocation context environment
      before ids (.values sources) after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.values sources) reached := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, by intro values same; cases same; exact ⟨.nil, admitted⟩⟩
  | single found generated =>
      cases execution with
      | cons head strict tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                by intro values same; cases same; exact ⟨.cons post.at_value.1 .nil, post.at_value.2⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head strict rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 rest
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.rows, by intro values same; cases same; exact ⟨.cons (firstPost.at_value.1.mono metadata) post.values_typed, post.at_values⟩⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : Trace budget program registry invocation context environment
      before ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.fault failure) reached := by
  induction tree generalizing mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed strict =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed strict =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head strict failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ strict
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 failed
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.at_fault_types⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Trace budget program registry invocation context environment before ids (.values sources) after →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Trace budget program registry invocation context environment before ids (.fault failure) after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
/-! A public Source call projects to its independent Dynamic callable outcome.
The same retained named function, dictionary, arguments and heap remain in the
conclusion. A stage rejection keeps its actual rejected source guard. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The named row and its complete independent successful application. -/
def PlainValue (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (value : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments value after

/-- Semantic failure retains its original reason and exact prefix heap. -/
def PlainFault (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    Dynamic.CallableFaults (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments reason after

variable {anchor header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap} {arguments : List Dynamic.Value}

theorem SourceCall.value_plain {value : Dynamic.Value}
    (trace : SourceCall anchor header invocation before arguments (.value value) after) :
    PlainValue anchor header invocation before arguments value after := by
  obtain ⟨rawD, function, size, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, applied.sound.value_plain⟩

theorem SourceCall.semanticFault_plain {reason : Dynamic.SemanticFault}
    (trace : SourceCall anchor header invocation before arguments (.fault (.semantic reason)) after) :
    PlainFault anchor header invocation before arguments reason after := by
  obtain ⟨rawD, function, size, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, applied.sound.semanticFault_plain⟩

/-- The original failure constructor determines which source judgment exists. -/
def FailureProjection (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  match failure with
  | .semantic reason => PlainFault anchor header invocation before arguments reason after
  | .stage origin call reason => Staging.Recursive.Generated origin call reason

theorem SourceCall.failure_plain {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation before arguments (.fault failure) after) :
    FailureProjection anchor header invocation before arguments failure after := by
  cases failure with
  | semantic reason => exact trace.semanticFault_plain
  | stage origin call reason =>
    obtain ⟨_rawD, _function, _size, _retained, applied⟩ := trace
    exact applied.sound.stage_origin rfl

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
end
