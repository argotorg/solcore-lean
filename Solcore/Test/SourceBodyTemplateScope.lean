import Solcore.SourceSemantics.SourceCompiledLocalCanonicalReadOrder
import Solcore.SourceSemantics.SourceCompiledLocalLexicalAllocation
import Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder
import Solcore.SourceSemantics.SourceCompiledBodyReadCutoff
import Solcore.SourceSemantics.SourceCompiledActualLocalReadCalls
import Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
import Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins
import Solcore.SourceSemantics.SourceCompiledActualTemplateBacking
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! Raw public compilation prepares a method containing nested generalized
lambdas and a nonempty qualified template. Both genuine catalog origins
supply their original checker body at the completed cache position. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceBodyTemplateScope
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceSemantics.CoreLowering

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, (Word, Bool)> { function coerce(flag: Bool) returns ((Word, Bool)) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; } }",

    "function entry(flag: Bool) returns (Word, Bool) { return flag; }"]}] }

def main : IO Unit := do
  let checked ← match checkProgram workspace 4096 with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"checker: {reprStr error}")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "entry")
    | throw (IO.userError "missing entry")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    match artifact : compiled.artifact? with
    | none => throw (IO.userError "missing completed artifact")
    | some cached =>
      have _actualBodies := SourceCompiledActualInitializerBarriers.compile_cached_bodies compiledEq artifact
      let mut ordinary := 0
      let mut methods := 0
      let mut methodTemplates := 0
      let mut templates := 0
      let mut variables := 0
      let mut separatedPairs := 0
      let mut localReadCalls := 0
      let mut generalizedReadCalls := 0
      let mut nestedOwners := 0
      let mut orderedLexicalReads := 0
      let mut orderedGeneralizedReads := 0
      for index in List.range cached.indexed.base.functions.length do
        match position : cached.indexed.base.functions[index]? with
        | none => throw (IO.userError "missing cache position")
        | some named =>
          have _actualScope := SourceBodyTemplateScope.cached_selection_scope artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have _actualGeneralizations := SourceCompiledLocalFinalization.BodySelection.cached_initialized_origins artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have _actualTemplateWitnesses := SourceCompiledLocalFinalization.BodySelection.cached_liveTemplatesBacked artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have exactCalls := SourceCompiledLocalFinalization.BodySelection.compile_local_read_calls
            compiledEq artifact position
          have _actualReadCutoff : ∃ selected : SourceCompiledLocalFinalization.BodySelection
              compiled named.specialized options.checkingFuel,
              SourceInferenceExecution.LocalReadCutoff selected.body.body.state := by
            obtain ⟨selected, _⟩ := exactCalls
            exact ⟨selected, selected.body_read_cutoff
              (SourceCoreCompiler.compile_checked_source compiledEq)⟩
          for retained in named.specialized.function.typedBody.nodes.attach do
            match nodeEq : retained.val with
            | .statement _ => pure ()
            | .expression node =>
              match form : node.form with
              | .reference name (.local binder) =>
                have nodeMember : .expression node ∈ named.specialized.function.typedBody.nodes := by
                  simpa only [nodeEq] using retained.property
                have _actualLookup : ∃ selected : SourceCompiledLocalFinalization.BodySelection compiled named.specialized options.checkingFuel,
                    SourceInferenceExecution.ActualLocalRead.Origin selected.inferenceCall node := by
                  obtain ⟨selected, calls⟩ := exactCalls
                  exact ⟨selected, calls node nodeMember name binder form⟩
                localReadCalls := localReadCalls + 1
                if (SourceSpecializationWorklist.localLambdaBindings named.specialized.function.typedBody).any
                    (fun binding => binding.binder.id == binder) then
                  generalizedReadCalls := generalizedReadCalls + 1
              | _ => pure ()
          match instancesAccepted : SourceSpecializationWorklist.localLambdaInstances named.specialized.function.typedBody with
          | .error error => throw (IO.userError s!"local instances: {reprStr error}")
          | .ok instances =>
            for localInstance in instances.attach do
              match bodyAccepted : SourceSpecializationWorklist.localLambdaBodyNodes
                  named.specialized.function.typedBody localInstance.val with
              | .error error => throw (IO.userError s!"local lexical body: {reprStr error}")
              | .ok bodyNodes =>
                let bodySource := {named.specialized.function.typedBody with nodes := bodyNodes}
                for nested in (initializedLetBindings bodySource).attach do
                  if different : nested.val.binder.id ≠ localInstance.val.binding.binder.id then
                    have _actualNestedOrder : nested.val.binder.id.binderIndex <
                        localInstance.val.binding.binder.id.binderIndex := by
                      obtain ⟨selected, _⟩ := exactCalls
                      exact selected.local_lambda_direct_initialized_binder_lt
                        (SourceCoreCompiler.compile_checked_source compiledEq)
                        (SourceSpecializationWorklist.localLambdaInstances_lexical_read_origin
                          instancesAccepted localInstance.val localInstance.property)
                        bodyAccepted nested.property different
                    unless nested.val.binder.id.binderIndex < localInstance.val.binding.binder.id.binderIndex do
                      throw (IO.userError "nested initialized owner is not before its containing declaration")
                    nestedOwners := nestedOwners + 1
                for retained in bodyNodes.attach do
                  match nodeEq : retained.val with
                  | .statement _ => pure ()
                  | .expression expression =>
                    match form : expression.form with
                    | .reference name (.local target) =>
                      have member : Node.expression expression ∈ bodyNodes := by
                        simpa only [nodeEq] using retained.property
                      have _actualOrder : target.binderIndex <
                          localInstance.val.binding.binder.id.binderIndex := by
                        obtain ⟨selected, _⟩ := exactCalls
                        have graph : OccurrenceGraphClosed named.specialized.function.typedBody := by
                          rw [selected.source]
                          exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
                            named.specialized.parameterSubstitution selected.body.resources.graph_closed
                        have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
                          graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist
                          bodyAccepted member
                        exact selected.local_lambda_descendant_read_binder_lt
                          (SourceCoreCompiler.compile_checked_source compiledEq)
                          (SourceSpecializationWorklist.localLambdaInstances_lexical_read_origin
                            instancesAccepted localInstance.val localInstance.property)
                          (SourceSpecializationWorklist.localLambdaBodyNodes_members bodyAccepted member)
                          path form
                      unless target.binderIndex < localInstance.val.binding.binder.id.binderIndex do
                        throw (IO.userError "actual local lexical read is not before its owner")
                      orderedLexicalReads := orderedLexicalReads + 1
                      if (SourceSpecializationWorklist.localLambdaBindings named.specialized.function.typedBody).any
                          (fun binding => binding.binder.id == target) then
                        orderedGeneralizedReads := orderedGeneralizedReads + 1
                    | _ => pure ()
          let original ← match compiled.program.functions.find?
              (fun function => function.declaration == named.specialized.function.declaration) with
            | some original =>
                ordinary := ordinary + 1
                pure original
            | none =>
                let some method := compiled.program.methods.find?
                    (fun method => method.checked.declaration == named.specialized.function.declaration)
                  | throw (IO.userError "cache body has no actual ordinary or method origin")
                methods := methods + 1
                methodTemplates := methodTemplates + (localSchemeTemplateOwners method.checked.typedBody).length
                pure method.checked
          for current in initializedLetBindings original.typedBody do
            for other in initializedLetBindings original.typedBody do
              if current.binder.id != other.binder.id &&
                  !current.binder.scheme.quantified.isEmpty && !other.binder.scheme.quantified.isEmpty then
                unless current.binder.scheme.quantified.all (fun q => !other.binder.scheme.quantified.contains q) do
                  throw (IO.userError "distinct initialized owners share a quantified variable")
                separatedPairs := separatedPairs + 1
          for owner in localSchemeTemplateOwners original.typedBody do
            let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
            unless free.all owner.binder.scheme.quantified.contains do
              throw (IO.userError "original body template escapes its complete owner")
            let some solved := original.solvedRequirements.find?
                (fun solved => solved.id == owner.requirement.templateRequirement)
              | throw (IO.userError "original body template has no solved row")
            unless solved.predicate == owner.requirement.predicate do
              throw (IO.userError "original body predicate changed in solved ledger")
            templates := templates + 1
            variables := variables + free.length
      unless compiled.plan.specializations.length == 1 && ordinary > 1 && methods > 0 && methodTemplates > 0 && templates > 0 && variables > 0 && separatedPairs > 0 && localReadCalls > 0 && generalizedReadCalls > 0 && orderedLexicalReads > 0 && orderedGeneralizedReads > 0 && nestedOwners > 0 do
        throw (IO.userError s!"method coverage changed: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, variables={variables}")
      IO.println s!"PASS cached ordinary and method template scope: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, flexible variables={variables}, separated owner pairs={separatedPairs}, exact local calls={localReadCalls}, generalized reads={generalizedReadCalls}, ordered lexical reads={orderedLexicalReads}, ordered generalized reads={orderedGeneralizedReads}, nested initialized owners={nestedOwners}"

end Tests.SourceBodyTemplateScope
