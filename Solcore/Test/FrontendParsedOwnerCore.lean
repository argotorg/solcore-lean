import Solcore.Frontend.ClosedSourceOwnerCoreBodyProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Syntax.Parser.Term

/- Actual parser, checker/lowering, raw evaluators and Core machine all run before
the ADR0314 bridges consume their complete mapped endpoints. -/
set_option autoImplicit false
namespace Tests.ADR0314ParsedOwnerCore
open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ADR0314ParsedOwnerCore",by decide⟩],by decide⟩⟩,n⟩
private def oldOwner := owner 314
private def foreignOwner := owner 914
private def lid (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o,n⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨a,same⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,owner] at impossible

private def expressionText := "x"
private def expressionFile : Syntax.SourceFile :=
  ⟨⟨.main,"adr0314-owner-core-expression.sol"⟩,expressionText⟩
private def bodyText :=
  "{let a:Unit=x;let b=a;match(tag){case 0{return b;}case _{return x;}}}"
private def bodyFile : Syntax.SourceFile :=
  ⟨⟨.main,"adr0314-owner-core-body.sol"⟩,bodyText⟩
private def span (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id,start,stop⟩
private def identifier (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Identifier := ⟨span file start stop,name⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨span file start stop,.identifier (identifier file start stop name)⟩
private def unitType (file : Syntax.SourceFile) (start stop : Nat) : Syntax.TypeExpr :=
  ⟨span file start stop,.named
    ⟨span file start stop,⟨⟨identifier file start stop "Unit",[]⟩⟩⟩ none⟩
private def returning (file : Syntax.SourceFile) (bs rs a b : Nat) (name : String) : Syntax.Block :=
  ⟨span file bs rs,[⟨span file a b,.returnStmt (some (reference file (b-2) (b-1) name))⟩]⟩
private def zeroCase : Syntax.MatchCase :=
  ⟨span bodyFile 33 50,⟨⟨span bodyFile 38 39,
    .literal ⟨span bodyFile 38 39,.decimal "0"⟩⟩,
    returning bodyFile 39 50 40 49 "b"⟩⟩
private def wildcardCase : Syntax.MatchCase :=
  ⟨span bodyFile 50 67,⟨⟨span bodyFile 55 56,.wildcard (span bodyFile 55 56)⟩,
    returning bodyFile 56 67 57 66 "x"⟩⟩
private def expectedExpression : Syntax.Expr := reference expressionFile 0 1 "x"
private def expectedBody : Syntax.Block :=
  ⟨span bodyFile 0 69,[
    ⟨span bodyFile 1 14,.letDecl (identifier bodyFile 5 6 "a")
      (some (unitType bodyFile 7 11)) (some (reference bodyFile 12 13 "x"))⟩,
    ⟨span bodyFile 14 22,.letDecl (identifier bodyFile 18 19 "b") none
      (some (reference bodyFile 20 21 "a"))⟩,
    ⟨span bodyFile 22 68,.matchWith
      ⟨span bodyFile 27 32,⟨reference bodyFile 28 31 "tag",[]⟩⟩
      ⟨span bodyFile 32 68,⟨[zeroCase,wildcardCase],none⟩⟩⟩]⟩
private def bodyRanges : List (Nat×Nat) :=
  [(0,69),(1,14),(5,6),(7,11),(7,11),(7,11),(12,13),(12,13),
   (14,22),(18,19),(20,21),(20,21),(22,68),(27,32),(28,31),(28,31),
   (32,68),(33,50),(38,39),(38,39),(39,50),(40,49),(47,48),(47,48),
   (50,67),(55,56),(55,56),(56,67),(57,66),(64,65),(64,65)]
private def bodySpans : List Syntax.SourceSpan := bodyRanges.map fun p => span bodyFile p.1 p.2

private structure ParsedExpression where
  source : Syntax.Expr
  gate : ClosedSourceDataExpression source
private structure ParsedBody where
  source : Syntax.Block
  gate : ClosedSourceDataBody source

private def parseExpression : IO ParsedExpression := do
  let .ok lexed := Syntax.Lexer.lex expressionFile | throw (IO.userError "expression lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial expressionFile lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==expressionFile && source.span==Syntax.SourceSpan.fullFile expressionFile &&
      source==expectedExpression && source.span.isValidFor expressionFile)
      "whole handwritten expression AST/spans/EOF/diagnostics"
    match shape : source with
    | ⟨_,.identifier _⟩ => return ⟨source,by rw [shape]; exact .reference⟩
    | _ => throw (IO.userError "expression gate shape")
  | _ => throw (IO.userError "expression parser")

private def parseBody : IO ParsedBody := do
  let .ok lexed := Syntax.Lexer.lex bodyFile | throw (IO.userError "body lexer")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial bodyFile lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      next.file==bodyFile && source.span==Syntax.SourceSpan.fullFile bodyFile &&
      source==expectedBody && bodySpans.all (fun s => s.isValidFor bodyFile))
      "whole handwritten body AST/all 31 spans/EOF/diagnostics"
    match shape : source with
    | ⟨_,[
        ⟨_,.letDecl _ (some _) (some ⟨_,.identifier _⟩)⟩,
        ⟨_,.letDecl _ none (some ⟨_,.identifier _⟩)⟩,
        ⟨_,.matchWith ⟨_,⟨⟨_,.identifier _⟩,[]⟩⟩
          ⟨_,⟨[
            ⟨_,⟨_,⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩⟩⟩,
            ⟨_,⟨_,⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩⟩⟩],none⟩⟩⟩]⟩ =>
      return ⟨source,by
        rw [shape]
        refine .binding .reference (.binding .reference (.wordMatch .reference ?_ ?_))
        · intro arm member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> exact .expression .reference
        · simp⟩
    | _ => throw (IO.userError "body gate shape")
  | _ => throw (IO.userError "body parser")

private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",lid oldOwner 7,.unit⟩,⟨"tag",lid foreignOwner 4,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit)]
private def zero : Core.Word := ⟨0,by decide⟩
private def one : Core.Word := ⟨1,by decide⟩
private def payload : Core.Value :=
  .closure .unit .word (.var 0) [.cellRef .unit 701,.hostFunction .storageWrite]
private def store : Core.Store :=
  [payload,.cellRef (.function .unit .word) 702,.hostFunction .storageRead]
private def environment (word : Core.Word) : Resolved.Environment :=
  [(lid oldOwner 7,payload),(lid foreignOwner 4,.word word)]
private def expressionEnvironment : Resolved.Environment :=
  environment zero ++ [(lid oldOwner 7,.unit),(lid foreignOwner 99,.hostFunction .storageWrite)]
private def up (e : Resolved.Environment) := e.map fun row => (row.1,RuntimeValue.ofCore row.2)

private def exerciseExpression (source : Syntax.Expr) (gate : ClosedSourceDataExpression source) : IO Unit := do
  let e := expressionEnvironment
  match resolvedRun : resolveLocalExpression? inputs.names source with
  | none => throw (IO.userError "actual old whole expression resolution")
  | some resolved =>
    let resolution := resolveLocalExpression?_sound resolvedRun
    match loweredRun : resolved.lower? e.ids with
    | none => throw (IO.userError "actual old whole expression lowering")
    | some core =>
      let lowered := Resolved.Expr.lower?_sound loweredRun
      let mapId := ownerLocalIdMap shift
      let mappedNames := LocalNameTable.mapIds mapId inputs.names
      let mappedEnvironment := Resolved.LocalScope.mapIds mapId e
      match mappedResolvedRun : resolveLocalExpression? mappedNames source with
      | none => throw (IO.userError "independent mapped whole expression resolution")
      | some mappedResolved =>
        match mappedLoweredRun : mappedResolved.lower? mappedEnvironment.ids with
        | none => throw (IO.userError "independent mapped whole expression lowering")
        | some mappedCore =>
          check (resolved==.var (lid oldOwner 7) && core==.var 0 &&
            mappedResolved==resolved.renameIds mapId && mappedCore==core)
            "complete old/mapped resolution and identical positional Core"
          match oldRun : evaluateClosedSourceExpression? 64 oldOwner inputs.names (up e)
              (store.map RuntimeValue.ofCore) source with
          | none => throw (IO.userError "actual old raw expression endpoint")
          | some (oldValue,oldFinal) =>
            let oldRaw := evaluateClosedSourceExpression?_sound oldRun
            match mappedRun : evaluateClosedSourceExpression? 64 (shift oldOwner) mappedNames
                (up mappedEnvironment) (store.map RuntimeValue.ofCore) source with
            | none => throw (IO.userError "actual owner-mapped raw expression endpoint")
            | some (mappedValue,mappedFinal) =>
              let mappedRaw := evaluateClosedSourceExpression?_sound mappedRun
              match coreRun : Core.runStateful 64 (.initial core e.values store) with
              | .done coreValue coreFinal =>
                let coreEval := Core.runStateful_evaluation_sound coreRun
                have oldImage := (gate.core_evaluates_iff resolution lowered).mp oldRaw
                have bridge := gate.mapOwners_core_evaluates_iff shift shift_injective
                  (actualValue:=mappedValue) (actualFinal:=mappedFinal) resolution lowered
                proof bridge.1; proof bridge.2.1
                have oldEndpoint : oldValue=RuntimeValue.ofCore coreValue ∧
                    oldFinal=coreFinal.map RuntimeValue.ofCore := by
                  obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := oldImage
                  obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
                  exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
                have mappedEndpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                    mappedFinal=coreFinal.map RuntimeValue.ofCore := by
                  obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := bridge.2.2.mp mappedRaw
                  obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
                  exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
                have mappedOfOld : mappedValue=oldValue.mapOwners shift := by
                  rw [oldEndpoint.1,mappedEndpoint.1,RuntimeValue.mapOwners_ofCore]
                have mappedStoreOfOld : mappedFinal=oldFinal.map (RuntimeValue.mapOwners shift) := by
                  rw [oldEndpoint.2,mappedEndpoint.2,mapRuntimeStoreOwners_ofCore]
                proof oldEndpoint; proof mappedEndpoint; proof mappedOfOld; proof mappedStoreOfOld
                check (oldValue.toCore?==some coreValue && mappedValue.toCore?==some coreValue &&
                  oldFinal.mapM RuntimeValue.toCore?==some coreFinal &&
                  mappedFinal.mapM RuntimeValue.toCore?==some coreFinal &&
                  coreFinal==store && mappedFinal.length==store.length)
                  "exact complete expression value and every final-store element"
              | _ => throw (IO.userError "actual Core expression evaluation")

private def exerciseBody (source : Syntax.Block) (gate : ClosedSourceDataBody source)
    (word : Core.Word) : IO Unit := do
  let e := environment word
  have sameIds : e.ids=inputs.context.ids := by rfl
  let mapId := ownerLocalIdMap shift
  let mappedInputs := inputs.mapIds mapId (ownerLocalIdMap_injective shift shift_injective)
  let mappedEnvironment := Resolved.LocalScope.mapIds mapId e
  match accepted : elaborateComputationReturnTree? elaborateLocalExpression? types oldOwner inputs source with
  | none => throw (IO.userError "actual old whole body checker")
  | some (core,type) =>
    match mappedAccepted : elaborateComputationReturnTree? elaborateLocalExpression? types
        (shift oldOwner) mappedInputs source with
    | none => throw (IO.userError "independent mapped whole body checker")
    | some (mappedCore,mappedType) =>
      check (type==.unit && mappedCore==core && mappedType==type &&
        Resolved.freshLocalId oldOwner inputs.ids==lid oldOwner 8 &&
        Resolved.freshLocalId oldOwner (lid oldOwner 8::inputs.ids)==lid oldOwner 9 &&
        Resolved.freshLocalId (shift oldOwner) mappedInputs.ids==lid (shift oldOwner) 8 &&
        Resolved.freshLocalId (shift oldOwner) (lid (shift oldOwner) 8::mappedInputs.ids)==
          lid (shift oldOwner) 9)
        "typed/inferred fresh bindings and complete old/mapped checker result"
      match oldRun : evaluateClosedSourceBody? 64 oldOwner inputs.names (up e)
          (store.map RuntimeValue.ofCore) source with
      | none => throw (IO.userError "actual old raw body endpoint")
      | some (oldValue,oldFinal) =>
        let oldRaw := evaluateClosedSourceBody?_sound oldRun
        match mappedRun : evaluateClosedSourceBody? 64 (shift oldOwner) mappedInputs.names
            (up mappedEnvironment) (store.map RuntimeValue.ofCore) source with
        | none => throw (IO.userError "actual owner-mapped raw body endpoint")
        | some (mappedValue,mappedFinal) =>
          let mappedRaw := evaluateClosedSourceBody?_sound mappedRun
          match coreRun : Core.runStateful 128 (.initial core e.values store) with
          | .done coreValue coreFinal =>
            let coreEval := Core.runStateful_evaluation_sound coreRun
            have oldImage := (gate.core_evaluates_iff accepted sameIds).mp oldRaw
            have bridge := gate.mapOwners_core_evaluates_iff shift shift_injective
              (environment:=e) (initialStore:=store) (actualValue:=mappedValue)
              (actualFinal:=mappedFinal) accepted sameIds
            proof bridge.1; proof bridge.2.1
            have oldEndpoint : oldValue=RuntimeValue.ofCore coreValue ∧
                oldFinal=coreFinal.map RuntimeValue.ofCore := by
              obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := oldImage
              obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
              exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
            have mappedEndpoint : mappedValue=RuntimeValue.ofCore coreValue ∧
                mappedFinal=coreFinal.map RuntimeValue.ofCore := by
              obtain ⟨imageValue,imageStore,hv,hs,ev⟩ := bridge.2.2.mp mappedRaw
              obtain ⟨sameValue,sameStore⟩ := Core.evaluation_deterministic ev coreEval
              exact ⟨hv.trans (congrArg _ sameValue),hs.trans (congrArg _ sameStore)⟩
            have mappedOfOld : mappedValue=oldValue.mapOwners shift := by
              rw [oldEndpoint.1,mappedEndpoint.1,RuntimeValue.mapOwners_ofCore]
            have mappedStoreOfOld : mappedFinal=oldFinal.map (RuntimeValue.mapOwners shift) := by
              rw [oldEndpoint.2,mappedEndpoint.2,mapRuntimeStoreOwners_ofCore]
            proof oldEndpoint; proof mappedEndpoint; proof mappedOfOld; proof mappedStoreOfOld
            check (oldValue.toCore?==some coreValue && mappedValue.toCore?==some coreValue &&
              oldFinal.mapM RuntimeValue.toCore?==some coreFinal &&
              mappedFinal.mapM RuntimeValue.toCore?==some coreFinal &&
              coreValue==payload && coreFinal==store && mappedFinal.length==store.length)
              "exact complete ordered-match body value and every final-store element"
          | _ => throw (IO.userError "actual Core body evaluation")

end Tests.ADR0314ParsedOwnerCore

open Solcore Tests.ADR0314ParsedOwnerCore in
def Tests.adr0314ParsedOwnerCoreConsumer : IO Unit := do
  proof shift_not_surjective
  check (!store.isEmpty && store.length==3 && expressionEnvironment.length==4)
    "nonempty complete store and duplicate/foreign expression rows"
  let expression ← parseExpression
  let body ← parseBody
  exerciseExpression expression.source expression.gate
  for word in [zero,one] do exerciseBody body.source body.gate word
  IO.println "ADR0314 parsed old/mapped raw endpoints and owner/Core bridges GREEN"
