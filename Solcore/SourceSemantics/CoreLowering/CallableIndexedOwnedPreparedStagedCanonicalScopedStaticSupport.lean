import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning

/-! General recursive expressions share the existing named scoped compiler
flow with legacy expressions and ordinary formation. Each canonical child
retains its actual compiler prefix; no runtime globals or body law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Existing recursive/formation certificates remain explicit alternatives.
The canonical branch retains only static root and compiler-prefix authority. -/
inductive Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | legacy {id lowered} (actual : CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
      header bodyRegistry semanticFaults context invocation scope id lowered) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id lowered
  | canonical {id lowered} (root : CanonicalRootAt compiled headers context invocation scope id lowered semanticFaults)
      («prefix» : root.compilation.administrativePrefix = 1) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id lowered
  | group {id node inner innerNode code}
      (metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked invocation.source id node code.type)
      (form : node.form = .group inner)
      (innerFound : invocation.source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Certificate headers header bodyRegistry semanticFaults context invocation scope inner code) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id code
  | tuple {id node ids types codes}
      (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
      (covers : invocation.evidence.Covers context)
      (actual : CompatibleExpressionTuples.Header (.initial compiled.compatible.checked) invocation.source id node ids types codes)
      (sequence : DataExpressionSequence.Tree invocation.source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Certificate headers header bodyRegistry semanticFaults context invocation scope child code) :
      Certificate headers header bodyRegistry semanticFaults context invocation scope id
        (SourceCoreCalls.packArguments codes)

/-- The same authentic branching receipt covers lexical bodies, branches and
finite loops. Collected retains its own compiler tree and catalog sites. -/
structure NamedSupport
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers header bodyRegistry semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
