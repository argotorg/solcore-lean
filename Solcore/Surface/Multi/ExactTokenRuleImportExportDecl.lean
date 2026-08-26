import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleImportExport
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldOptionalAliasPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalAliasPlan
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown alias helper"

elab "unfoldOptionalPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown option helper"

elab "rwDeclarationPlansMapM" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.plans?_eq_mapM
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      let identifier := mkIdent declaration
      rewriteTarget identifier.raw false
  | _ => throwError "the declaration visitor has an unknown list theorem"

elab "unfoldMarkerPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.markerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown marker helper"

elab "unfoldRemoteSelectionAfterReferenceCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.remoteSelectionAfterReferencePlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown remote helper"

private abbrev importDeclBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)),
    .list0 (.atom (.nonterminal .importEntry)),
    .atom (.terminal (.symbol .rightBrace)),
    .optional (.atom (.nonterminal .hidingClause)),
    .atom (.terminal (.symbol .semicolon))]]

private abbrev importDeclModuleChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .importKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.symbol .semicolon))]

private abbrev importDeclAliasChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .importKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.hardKeyword .asKw)),
  .atom (.terminal (.category .identifier)),
  .atom (.terminal (.symbol .semicolon))]

private abbrev importDeclItemsChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .importKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.symbol .dot)),
  .atom (.terminal (.symbol .leftBrace)),
  .list0 (.atom (.nonterminal .importEntry)),
  .atom (.terminal (.symbol .rightBrace)),
  .optional (.atom (.nonterminal .hidingClause)),
  .atom (.terminal (.symbol .semicolon))]

private abbrev exportDeclBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.terminal (.symbol .leftBrace)),
    .list0 (.atom (.nonterminal .localExportEntry)),
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .semicolon))],
  .sequence [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)),
    .list0 (.atom (.nonterminal .remoteExportEntry)),
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]]

private abbrev exportDeclLocalChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .exportKw)),
  .atom (.terminal (.symbol .leftBrace)),
  .list0 (.atom (.nonterminal .localExportEntry)),
  .atom (.terminal (.symbol .rightBrace)),
  .atom (.terminal (.symbol .semicolon))]

private abbrev exportDeclModuleChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .exportKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.symbol .semicolon))]

private abbrev exportDeclAliasChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .exportKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.hardKeyword .asKw)),
  .atom (.terminal (.category .identifier)),
  .atom (.terminal (.symbol .semicolon))]

private abbrev exportDeclWildcardChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .exportKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.symbol .dot)),
  .atom (.terminal (.symbol .star)),
  .atom (.terminal (.symbol .semicolon))]

private abbrev exportDeclBracedChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .exportKw)),
  .atom (.nonterminal .moduleRef),
  .atom (.terminal (.symbol .dot)),
  .atom (.terminal (.symbol .leftBrace)),
  .list0 (.atom (.nonterminal .remoteExportEntry)),
  .atom (.terminal (.symbol .rightBrace)),
  .atom (.terminal (.symbol .semicolon))]

private theorem importDeclModuleInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importDeclBranches
        ⟨⟨0, by decide⟩,
          EbnfValue.sequence importDeclModuleChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                  EbnfValues.nil)))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      pure (TokenPlan.concat [
        .exact (.hardKeyword .importKw) importKw.span,
        referencePlan,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice importDeclBranches
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence importDeclModuleChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence importDeclModuleChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                EbnfValues.nil)))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      cases moduleReferencePlan? reference <;>
        simp [TokenPlan.concat_cons]

private theorem identifierPhysicalPlan_eq
    {file : WorkspaceFile} {tokens : List Token}
    (data : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (projects : IdentifierProjects data.matched data.spelling data.parsed) :
    data.matched.physicalTokenPlan =
      identifierPlan
        (RuleReduction.terminalLoc data.matched data.parsed) := by
  rcases projects with ⟨token, valueEq, payloadEq, parseEq⟩
  have spellingEq : data.spelling = data.parsed.render := by
    unfold Identifier.parse at parseEq
    split at parseEq
    · simpa [Identifier.render] using
        congrArg Identifier.text (Option.some.inj parseEq)
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, valueEq,
    identifierPlan, RuleReduction.terminalLoc, ← spellingEq, payloadEq]

private theorem importDeclAliasedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importDeclBranches
        ⟨⟨1, by decide⟩,
          EbnfValue.sequence importDeclAliasChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.category .identifier) name.matched)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .semicolon) semicolon)
                      EbnfValues.nil)))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      pure (TokenPlan.concat [
        .exact (.hardKeyword .importKw) importKw.span,
        referencePlan,
        .exact (.hardKeyword .asKw) asKw.span,
        identifierPlan (RuleReduction.terminalLoc name.matched name.parsed),
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice importDeclBranches
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence importDeclAliasChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.category .identifier) name.matched)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .semicolon) semicolon)
                        EbnfValues.nil)))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence importDeclAliasChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom
                    (.category .identifier) name.matched)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      rw [identifierPhysicalPlan_eq name nameProjects]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      cases moduleReferencePlan? reference <;>
        simp [TokenPlan.concat_cons]

private theorem importEntryRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (RuleValue .importEntry)) :
    (entries.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .importEntry)).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      entries.mapM (ruleTokenPlan? .importEntry) := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout]

private theorem optionalHidingInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (value : Option (RuleValue .hidingClause)) :
    (EbnfValue.optional
      (file := file) (tokens := tokens)
      (.atom (.nonterminal .hidingClause))
      (value.map (EbnfValue.ruleAtom .hidingClause))).tokenPlan?
        { plan? := ruleTokenPlan? } =
      match value with
      | none => some TokenPlan.empty
      | some clause => ruleTokenPlan? .hidingClause clause := by
  cases value with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
  | some clause =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_ruleAtom]

private def importHidingCandidate
    (value : Option (RuleValue .hidingClause)) : Option TokenPlan :=
  match value with
  | none => some TokenPlan.empty
  | some clause => ruleTokenPlan? .hidingClause clause

private def importHidingOutput
    (value : Option HidingClause) : Option TokenPlan :=
  match value with
  | none => some TokenPlan.empty
  | some clause => hidingClausePlan? clause

private theorem importHidingCandidate_eq_output
    (value : Option HidingClause) :
    importHidingCandidate value = importHidingOutput value := by
  cases value <;> rfl

private theorem importEntryRulePlans_eq
    (entries : List ImportSelectorEntry) :
    entries.mapM (ruleTokenPlan? .importEntry) =
      entries.mapM importSelectorEntryPlan? := by
  rfl

private theorem importDeclItemsInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List (RuleValue .importEntry))
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option (RuleValue .hidingClause))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importDeclBranches
        ⟨⟨2, by decide⟩,
          EbnfValue.sequence importDeclItemsChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .dot) dot)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                    (EbnfValues.cons _ _
                      (EbnfValue.list0 _
                        (entries.map (EbnfValue.ruleAtom .importEntry)))
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .rightBrace) closeBrace)
                        (EbnfValues.cons _ _
                          (EbnfValue.optional _
                            (hidingValue.map
                              (EbnfValue.ruleAtom .hidingClause)))
                          (EbnfValues.cons _ _
                            (EbnfValue.terminalAtom
                              (.symbol .semicolon) semicolon)
                            EbnfValues.nil))))))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      let entryPlans ← entries.mapM (ruleTokenPlan? .importEntry)
      let hidingPlan ← importHidingCandidate hidingValue
      pure (TokenPlan.concat [
        .exact (.hardKeyword .importKw) importKw.span,
        referencePlan,
        .exact (.symbol .dot) dot.span,
        .exact (.symbol .leftBrace) openBrace.span,
        .commaSeparated entryPlans,
        .exact (.symbol .rightBrace) closeBrace.span,
        hidingPlan,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice importDeclBranches
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence importDeclItemsChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .dot) dot)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.list0 _
                          (entries.map (EbnfValue.ruleAtom .importEntry)))
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.symbol .rightBrace) closeBrace)
                          (EbnfValues.cons _ _
                            (EbnfValue.optional _
                              (hidingValue.map
                                (EbnfValue.ruleAtom .hidingClause)))
                            (EbnfValues.cons _ _
                              (EbnfValue.terminalAtom
                                (.symbol .semicolon) semicolon)
                              EbnfValues.nil))))))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence importDeclItemsChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .importKw) importKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .dot) dot)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                  (EbnfValues.cons _ _
                    (EbnfValue.list0 _
                      (entries.map (EbnfValue.ruleAtom .importEntry)))
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .rightBrace) closeBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.optional _
                          (hidingValue.map
                            (EbnfValue.ruleAtom .hidingClause)))
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.symbol .semicolon) semicolon)
                          EbnfValues.nil))))))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_list0,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      rw [importEntryRuleValues_mapM_tokenPlan? entries,
        optionalHidingInput_tokenPlan? hidingValue]
      cases hidingValue with
      | none =>
          simp only [importHidingCandidate]
          cases moduleReferencePlan? reference <;>
            cases entries.mapM (ruleTokenPlan? .importEntry) <;>
              simp [TokenPlan.concat_cons, TokenPlan.append_assoc]
      | some clause =>
          simp only [importHidingCandidate]
          cases moduleReferencePlan? reference <;>
            cases entries.mapM (ruleTokenPlan? .importEntry) <;>
              cases clauseEq : ruleTokenPlan? .hidingClause clause <;>
                simp [clauseEq, TokenPlan.concat_cons,
                  TokenPlan.append_assoc]

private theorem TokenSlot.ListMatches.concatExactToPlain
    {kind : TokenKind} {span : SourceSpan}
    {before after : List TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.exact kind span] ++ after)).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.plain kind] ++ after)).slots actual := by
  have normalized : TokenSlot.ListMatches
      ((TokenPlan.concat before).append
        ((TokenPlan.exact kind span).append
          (TokenPlan.concat after))).slots actual := by
    simpa [TokenPlan.concat, TokenPlan.append, List.flatMap_append]
      using relation
  have weakened := TokenSlot.ListMatches.exactBetweenToPlain normalized
  simpa [TokenPlan.concat, TokenPlan.append, List.flatMap_append]
    using weakened

private theorem TokenSlot.lastSatisfies_append_singleton_local
    (constraint : TokenSpanConstraint) (initial : List Token)
    (last : Token) :
    TokenSlot.LastSatisfies constraint (initial ++ [last]) ↔
      constraint.Holds last := by
  induction initial with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          change TokenSlot.LastSatisfies constraint
            (next :: rest ++ [last]) ↔ constraint.Holds last
          exact induction

private theorem TokenSlot.ListMatches.exactBookendsToEnclosedPlain
    {file : WorkspaceFile}
    {firstKind lastKind : TokenKind}
    {firstSpan lastSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (firstValid : firstSpan.ValidFor file)
    (lastValid : lastSpan.ValidFor file)
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.exact firstKind firstSpan,
        middle,
        TokenPlan.exact lastKind lastSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.enclose
        (RuleReduction.between file firstSpan lastSpan ()).span
        (TokenPlan.concat [
          TokenPlan.plain firstKind,
          middle,
          TokenPlan.plain lastKind])).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, List.append_nil,
    List.singleton_append] at relation
  cases relation with
  | @required _ firstToken _ _ firstMatch rest =>
      rcases rest.split_append with
        ⟨middleActual, lastActual, rfl,
          middleRelation, lastRelation⟩
      cases lastRelation with
      | @required _ lastToken _ _ lastMatch tail =>
          cases tail
          let inner := TokenPlan.concat [
            TokenPlan.plain firstKind,
            middle,
            TokenPlan.plain lastKind]
          have innerRelation : TokenSlot.ListMatches inner.slots
              (firstToken :: middleActual ++ [lastToken]) := by
            exact .required firstMatch.toPlain <|
              middleRelation.append <|
                .required lastMatch.toPlain .nil
          have starts : TokenSlot.FirstSatisfies
              (.starts (RuleReduction.between
                file firstSpan lastSpan ()).span)
              (firstToken :: middleActual ++ [lastToken]) := by
            have exactSpan : firstToken.span = firstSpan :=
              firstMatch.2 (.exact firstSpan) (by simp [ExpectedToken.exact])
            change firstToken.span.source = file.id ∧
              firstToken.span.startByte = firstSpan.startByte
            rw [exactSpan]
            exact ⟨firstValid.1, rfl⟩
          have ends : TokenSlot.LastSatisfies
              (.ends (RuleReduction.between
                file firstSpan lastSpan ()).span)
              (firstToken :: middleActual ++ [lastToken]) := by
            have exactSpan : lastToken.span = lastSpan :=
              lastMatch.2 (.exact lastSpan) (by simp [ExpectedToken.exact])
            rw [TokenSlot.lastSatisfies_append_singleton_local]
            change lastToken.span.source = file.id ∧
              lastToken.span.endByte = lastSpan.endByte
            rw [exactSpan]
            exact ⟨lastValid.1, rfl⟩
          exact TokenSlot.ListMatches.enclose innerRelation
            (by
              exact TokenPlan.WellAnchored.concatPlainBookended
                firstKind lastKind [middle])
            starts ends

private theorem TokenSlot.ListMatches.concatBookendsToEnclosedPlain
    {file : WorkspaceFile}
    {firstKind lastKind : TokenKind}
    {firstSpan lastSpan : SourceSpan}
    {before after : List TokenPlan}
    {middle : TokenPlan} {actual : List Token}
    (firstValid : firstSpan.ValidFor file)
    (lastValid : lastSpan.ValidFor file)
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.exact firstKind firstSpan, middle,
          TokenPlan.exact lastKind lastSpan] ++ after)).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.enclose
          (RuleReduction.between file firstSpan lastSpan ()).span
          (TokenPlan.concat [
            TokenPlan.plain firstKind,
            middle,
            TokenPlan.plain lastKind])] ++ after)).slots actual := by
  let beforePlan := TokenPlan.concat before
  let segmentPlan := TokenPlan.concat [
    TokenPlan.exact firstKind firstSpan,
    middle,
    TokenPlan.exact lastKind lastSpan]
  let afterPlan := TokenPlan.concat after
  have normalized : TokenSlot.ListMatches
      (beforePlan.append (segmentPlan.append afterPlan)).slots actual := by
    simpa [beforePlan, segmentPlan, afterPlan, TokenPlan.concat, TokenPlan.append,
      List.flatMap_append] using relation
  rcases normalized.split_append with
    ⟨prefixActual, remainderActual, rfl,
      prefixRelation, remainderRelation⟩
  rcases remainderRelation.split_append with
    ⟨segmentActual, suffixActual, rfl,
      segmentRelation, suffixRelation⟩
  have transformed :=
    TokenSlot.ListMatches.exactBookendsToEnclosedPlain
      firstValid lastValid segmentRelation
  have joined := prefixRelation.append (transformed.append suffixRelation)
  simpa [beforePlan, segmentPlan, afterPlan, TokenPlan.concat, TokenPlan.append,
    List.flatMap_append] using joined

private theorem TokenSlot.ListMatches.exactBookendsToEnclosedPlainExact
    {file : WorkspaceFile}
    {firstKind lastKind : TokenKind}
    {firstSpan lastSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (firstValid : firstSpan.ValidFor file)
    (lastValid : lastSpan.ValidFor file)
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.exact firstKind firstSpan,
        middle,
        TokenPlan.exact lastKind lastSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.enclose
        (RuleReduction.between file firstSpan lastSpan ()).span
        (TokenPlan.concat [
          TokenPlan.plain firstKind,
          middle,
          TokenPlan.exact lastKind lastSpan])).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, List.append_nil,
    List.singleton_append] at relation
  cases relation with
  | @required _ firstToken _ _ firstMatch rest =>
      rcases rest.split_append with
        ⟨middleActual, lastActual, rfl,
          middleRelation, lastRelation⟩
      cases lastRelation with
      | @required _ lastToken _ _ lastMatch tail =>
          cases tail
          let inner := TokenPlan.concat [
            TokenPlan.plain firstKind,
            middle,
            TokenPlan.exact lastKind lastSpan]
          have innerRelation : TokenSlot.ListMatches inner.slots
              (firstToken :: middleActual ++ [lastToken]) := by
            exact .required firstMatch.toPlain <|
              middleRelation.append <|
                .required lastMatch .nil
          have starts : TokenSlot.FirstSatisfies
              (.starts (RuleReduction.between
                file firstSpan lastSpan ()).span)
              (firstToken :: middleActual ++ [lastToken]) := by
            have exactSpan : firstToken.span = firstSpan :=
              firstMatch.2 (.exact firstSpan) (by simp [ExpectedToken.exact])
            change firstToken.span.source = file.id ∧
              firstToken.span.startByte = firstSpan.startByte
            rw [exactSpan]
            exact ⟨firstValid.1, rfl⟩
          have ends : TokenSlot.LastSatisfies
              (.ends (RuleReduction.between
                file firstSpan lastSpan ()).span)
              (firstToken :: middleActual ++ [lastToken]) := by
            have exactSpan : lastToken.span = lastSpan :=
              lastMatch.2 (.exact lastSpan) (by simp [ExpectedToken.exact])
            rw [TokenSlot.lastSatisfies_append_singleton_local]
            change lastToken.span.source = file.id ∧
              lastToken.span.endByte = lastSpan.endByte
            rw [exactSpan]
            exact ⟨lastValid.1, rfl⟩
          have innerAnchored : inner.WellAnchored := by
            apply TokenPlan.WellAnchored.of_starts_ends_append
              (left := TokenPlan.plain firstKind)
              (right := TokenPlan.concat [middle,
                TokenPlan.exact lastKind lastSpan])
            · exact TokenPlan.WellAnchored.StartsRequired.concat_plain_first
                firstKind []
            · exact TokenPlan.WellAnchored.EndsRequired.concat_exact_last
                [middle] lastKind lastSpan
          exact TokenSlot.ListMatches.enclose innerRelation
            innerAnchored starts ends

private theorem TokenSlot.ListMatches.concatBookendsToEnclosedPlainExact
    {file : WorkspaceFile}
    {firstKind lastKind : TokenKind}
    {firstSpan lastSpan : SourceSpan}
    {before after : List TokenPlan}
    {middle : TokenPlan} {actual : List Token}
    (firstValid : firstSpan.ValidFor file)
    (lastValid : lastSpan.ValidFor file)
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.exact firstKind firstSpan, middle,
          TokenPlan.exact lastKind lastSpan] ++ after)).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat
        (before ++ [TokenPlan.enclose
          (RuleReduction.between file firstSpan lastSpan ()).span
          (TokenPlan.concat [
            TokenPlan.plain firstKind,
            middle,
            TokenPlan.exact lastKind lastSpan])] ++ after)).slots actual := by
  let beforePlan := TokenPlan.concat before
  let segmentPlan := TokenPlan.concat [
    TokenPlan.exact firstKind firstSpan,
    middle,
    TokenPlan.exact lastKind lastSpan]
  let afterPlan := TokenPlan.concat after
  have normalized : TokenSlot.ListMatches
      (beforePlan.append (segmentPlan.append afterPlan)).slots actual := by
    simpa [beforePlan, segmentPlan, afterPlan, TokenPlan.concat,
      TokenPlan.append, List.flatMap_append] using relation
  rcases normalized.split_append with
    ⟨beforeActual, remainderActual, rfl,
      beforeRelation, remainderRelation⟩
  rcases remainderRelation.split_append with
    ⟨segmentActual, afterActual, rfl,
      segmentRelation, afterRelation⟩
  have transformed :=
    TokenSlot.ListMatches.exactBookendsToEnclosedPlainExact
      firstValid lastValid segmentRelation
  have joined := beforeRelation.append (transformed.append afterRelation)
  simpa [beforePlan, segmentPlan, afterPlan, TokenPlan.concat,
    TokenPlan.append, List.flatMap_append] using joined

private theorem localExportRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (RuleValue .localExportEntry)) :
    (entries.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .localExportEntry)).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      entries.mapM (ruleTokenPlan? .localExportEntry) := by
  rw [List.mapM_map]
  simp [Function.comp_def]

private theorem remoteExportRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (RuleValue .remoteExportEntry)) :
    (entries.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .remoteExportEntry)).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      entries.mapM (ruleTokenPlan? .remoteExportEntry) := by
  rw [List.mapM_map]
  simp [Function.comp_def]

private theorem localExportRulePlans_eq
    (entries : List ExportEntry) :
    entries.mapM (ruleTokenPlan? .localExportEntry) =
      entries.mapM localExportEntryPlan? := by
  rfl

private theorem remoteExportRulePlans_eq
    (entries : List RemoteExportEntry) :
    entries.mapM (ruleTokenPlan? .remoteExportEntry) =
      entries.mapM remoteExportEntryPlan? := by
  rfl

private theorem exportDeclModuleInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice exportDeclBranches
        ⟨⟨1, by decide⟩,
          EbnfValue.sequence exportDeclModuleChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                  EbnfValues.nil)))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      pure (TokenPlan.concat [
        .exact (.hardKeyword .exportKw) exportKw.span,
        referencePlan,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice exportDeclBranches
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence exportDeclModuleChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence exportDeclModuleChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
                EbnfValues.nil)))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      cases moduleReferencePlan? reference <;>
        simp [TokenPlan.concat_cons]

private theorem exportDeclAliasedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice exportDeclBranches
        ⟨⟨2, by decide⟩,
          EbnfValue.sequence exportDeclAliasChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.category .identifier) name.matched)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .semicolon) semicolon)
                      EbnfValues.nil)))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      pure (TokenPlan.concat [
        .exact (.hardKeyword .exportKw) exportKw.span,
        referencePlan,
        .exact (.hardKeyword .asKw) asKw.span,
        identifierPlan (RuleReduction.terminalLoc name.matched name.parsed),
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice exportDeclBranches
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence exportDeclAliasChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.category .identifier) name.matched)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .semicolon) semicolon)
                        EbnfValues.nil)))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence exportDeclAliasChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .asKw) asKw)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom
                    (.category .identifier) name.matched)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      rw [identifierPhysicalPlan_eq name nameProjects]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      cases moduleReferencePlan? reference <;>
        simp [TokenPlan.concat_cons]

private theorem exportDeclWildcardInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice exportDeclBranches
        ⟨⟨3, by decide⟩,
          EbnfValue.sequence exportDeclWildcardChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .dot) dot)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .star) star)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .semicolon) semicolon)
                      EbnfValues.nil)))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      pure (TokenPlan.concat [
        .exact (.hardKeyword .exportKw) exportKw.span,
        referencePlan,
        .exact (.symbol .dot) dot.span,
        .exact (.symbol .star) star.span,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice exportDeclBranches
          ⟨⟨3, by decide⟩,
            EbnfValue.sequence exportDeclWildcardChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .dot) dot)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom (.symbol .star) star)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .semicolon) semicolon)
                        EbnfValues.nil)))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence exportDeclWildcardChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .dot) dot)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .star) star)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq]
      cases moduleReferencePlan? reference <;>
        simp [TokenPlan.concat_cons]

private theorem exportDeclLocalInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List (RuleValue .localExportEntry))
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice exportDeclBranches
        ⟨⟨0, by decide⟩,
          EbnfValue.sequence exportDeclLocalChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                (EbnfValues.cons _ _
                  (EbnfValue.list0 _
                    (entries.map
                      (EbnfValue.ruleAtom .localExportEntry)))
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .rightBrace) closeBrace)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .semicolon) semicolon)
                      EbnfValues.nil)))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let entryPlans ← entries.mapM (ruleTokenPlan? .localExportEntry)
      pure (TokenPlan.concat [
        .exact (.hardKeyword .exportKw) exportKw.span,
        .exact (.symbol .leftBrace) openBrace.span,
        .commaSeparated entryPlans,
        .exact (.symbol .rightBrace) closeBrace.span,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice exportDeclBranches
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence exportDeclLocalChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                  (EbnfValues.cons _ _
                    (EbnfValue.list0 _
                      (entries.map
                        (EbnfValue.ruleAtom .localExportEntry)))
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .rightBrace) closeBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .semicolon) semicolon)
                        EbnfValues.nil)))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence exportDeclLocalChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
              (EbnfValues.cons _ _
                (EbnfValue.list0 _
                  (entries.map
                    (EbnfValue.ruleAtom .localExportEntry)))
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom
                    (.symbol .rightBrace) closeBrace)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .semicolon) semicolon)
                    EbnfValues.nil)))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list0,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      rw [localExportRuleValues_mapM_tokenPlan? entries]
      cases entries.mapM (ruleTokenPlan? .localExportEntry) <;>
        simp [TokenPlan.concat_cons, TokenPlan.append_assoc]

private theorem exportDeclBracedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List (RuleValue .remoteExportEntry))
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice exportDeclBranches
        ⟨⟨4, by decide⟩,
          EbnfValue.sequence exportDeclBracedChildren
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .dot) dot)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                    (EbnfValues.cons _ _
                      (EbnfValue.list0 _
                        (entries.map
                          (EbnfValue.ruleAtom .remoteExportEntry)))
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .rightBrace) closeBrace)
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.symbol .semicolon) semicolon)
                          EbnfValues.nil)))))))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let referencePlan ← moduleReferencePlan? reference
      let entryPlans ← entries.mapM (ruleTokenPlan? .remoteExportEntry)
      pure (TokenPlan.concat [
        .exact (.hardKeyword .exportKw) exportKw.span,
        referencePlan,
        .exact (.symbol .dot) dot.span,
        .exact (.symbol .leftBrace) openBrace.span,
        .commaSeparated entryPlans,
        .exact (.symbol .rightBrace) closeBrace.span,
        .exact (.symbol .semicolon) semicolon.span])) := by
  calc
    _ = (EbnfValue.choice exportDeclBranches
          ⟨⟨4, by decide⟩,
            EbnfValue.sequence exportDeclBracedChildren
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
                (EbnfValues.cons _ _
                  (EbnfValue.ruleAtom .moduleRef reference)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .dot) dot)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.list0 _
                          (entries.map
                            (EbnfValue.ruleAtom .remoteExportEntry)))
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.symbol .rightBrace) closeBrace)
                          (EbnfValues.cons _ _
                            (EbnfValue.terminalAtom
                              (.symbol .semicolon) semicolon)
                            EbnfValues.nil)))))))⟩).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence exportDeclBracedChildren
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.hardKeyword .exportKw) exportKw)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .dot) dot)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
                  (EbnfValues.cons _ _
                    (EbnfValue.list0 _
                      (entries.map
                        (EbnfValue.ruleAtom .remoteExportEntry)))
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .rightBrace) closeBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .semicolon) semicolon)
                        EbnfValues.nil)))))))).tokenPlan?
          sourceRuleTokenPlanLayout :=
      EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_list0,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout]
      have modulePlanEq : ruleTokenPlan? .moduleRef reference =
          moduleReferencePlan? reference := rfl
      rw [modulePlanEq,
        remoteExportRuleValues_mapM_tokenPlan? entries]
      cases moduleReferencePlan? reference <;>
        cases entries.mapM (ruleTokenPlan? .remoteExportEntry) <;>
          simp [TokenPlan.concat_cons, TokenPlan.append_assoc]

/-- Every import declaration preserves its module reference, optional alias,
item selection, optional hiding clause, delimiters, and enclosing span. -/
theorem importDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .importDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | importDeclModule origin finish importKw reference semicolon witness =>
      change EbnfValue file tokens (.choice importDeclBranches) at input
      rw [← inputEq] at inputEvidence
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none := by
            rw [inputEq]
            exact (importDeclModuleInput_tokenPlan?
              importKw reference semicolon).trans (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .importKw) importKw.span,
                  referencePlan,
                  .exact (.symbol .semicolon) semicolon.span]) := by
            rw [inputEq]
            exact (importDeclModuleInput_tokenPlan?
              importKw reference semicolon).trans (by simp [referenceEq])
          have sourceEvidence : TokenPlanEvidence
              (some (TokenPlan.concat [
                .exact (.hardKeyword .importKw) importKw.span,
                referencePlan,
                .exact (.symbol .semicolon) semicolon.span]))
              (PhysicalTokens tokens origin finish) := by
            exact inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, candidateEq, relation⟩
          simp only [Option.some.injEq] at candidateEq
          subst sourcePlan
          have afterKeyword := relation.concatExactToPlain
            (before := [])
            (after := [referencePlan,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterKeyword.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .importKw),
              referencePlan]) (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .importKw),
            referencePlan,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .importKw) (.symbol .semicolon)
              [referencePlan]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan success => by
              simp only [Option.some.injEq] at success
              subst plan
              exact innerAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, importDeclPlan?, sourceLoc,
            referenceEq, Option.bind_some]
          unfoldOptionalAliasPlanCore
          simp [inner, TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | importDeclAliased origin finish importKw reference asKw name semicolon
      nameProjects witness =>
      change EbnfValue file tokens (.choice importDeclBranches) at input
      rw [← inputEq] at inputEvidence
      let nameLoc := RuleReduction.terminalLoc name.matched name.parsed
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none := by
            rw [inputEq]
            exact (importDeclAliasedInput_tokenPlan?
              importKw reference asKw name semicolon nameProjects).trans
                (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .importKw) importKw.span,
                  referencePlan,
                  .exact (.hardKeyword .asKw) asKw.span,
                  identifierPlan nameLoc,
                  .exact (.symbol .semicolon) semicolon.span]) := by
            rw [inputEq]
            exact (importDeclAliasedInput_tokenPlan?
              importKw reference asKw name semicolon nameProjects).trans
                (by simp [referenceEq, nameLoc])
          have sourceEvidence := inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst sourcePlan
          have afterImport := relation.concatExactToPlain
            (before := [])
            (after := [referencePlan,
              TokenPlan.exact (.hardKeyword .asKw) asKw.span,
              identifierPlan nameLoc,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have afterAs := afterImport.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .importKw),
              referencePlan])
            (after := [identifierPlan nameLoc,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterAs.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .importKw),
              referencePlan, TokenPlan.plain (.hardKeyword .asKw),
              identifierPlan nameLoc])
            (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .importKw),
            referencePlan,
            TokenPlan.plain (.hardKeyword .asKw),
            identifierPlan nameLoc,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .importKw) (.symbol .semicolon)
              [referencePlan, TokenPlan.plain (.hardKeyword .asKw),
                identifierPlan nameLoc]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan planEq => by
              simp only [Option.some.injEq] at planEq
              subst plan
              exact innerAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, importDeclPlan?, sourceLoc,
            referenceEq]
          unfoldOptionalAliasPlanCore
          simp [nameLoc, inner, TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | importDeclItems origin finish importKw reference dot openBrace entries
      closeBrace hidingValue semicolon witness =>
      change EbnfValue file tokens (.choice importDeclBranches) at input
      rw [← inputEq] at inputEvidence
      have rawCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let referencePlan ← moduleReferencePlan? reference
            let entryPlans ← entries.mapM (ruleTokenPlan? .importEntry)
            let hidingPlan ← importHidingCandidate hidingValue
            pure (TokenPlan.concat [
              .exact (.hardKeyword .importKw) importKw.span,
              referencePlan,
              .exact (.symbol .dot) dot.span,
              .exact (.symbol .leftBrace) openBrace.span,
              .commaSeparated entryPlans,
              .exact (.symbol .rightBrace) closeBrace.span,
              hidingPlan,
              .exact (.symbol .semicolon) semicolon.span])) := by
        rw [inputEq]
        exact importDeclItemsInput_tokenPlan?
          importKw reference dot openBrace entries closeBrace
            hidingValue semicolon
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none :=
            rawCandidateEq.trans (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          cases entriesEq : entries.mapM (ruleTokenPlan? .importEntry) with
          | none =>
              have candidateEq :
                  input.tokenPlan? sourceRuleTokenPlanLayout = none :=
                rawCandidateEq.trans (by simp [referenceEq, entriesEq])
              have noneEvidence := inputEvidence.candidate_eq candidateEq
              rcases noneEvidence with ⟨plan, success, relation⟩
              contradiction
          | some entryPlans =>
              cases hidingEq : importHidingCandidate hidingValue with
              | none =>
                  have candidateEq :
                      input.tokenPlan? sourceRuleTokenPlanLayout = none :=
                    rawCandidateEq.trans
                      (by simp [referenceEq, entriesEq, hidingEq])
                  have noneEvidence := inputEvidence.candidate_eq candidateEq
                  rcases noneEvidence with ⟨plan, success, relation⟩
                  contradiction
              | some hidingPlan =>
                  have candidateEq :
                      input.tokenPlan? sourceRuleTokenPlanLayout =
                        some (TokenPlan.concat [
                          .exact (.hardKeyword .importKw) importKw.span,
                          referencePlan,
                          .exact (.symbol .dot) dot.span,
                          .exact (.symbol .leftBrace) openBrace.span,
                          .commaSeparated entryPlans,
                          .exact (.symbol .rightBrace) closeBrace.span,
                          hidingPlan,
                          .exact (.symbol .semicolon) semicolon.span]) :=
                    rawCandidateEq.trans
                      (by simp [referenceEq, entriesEq, hidingEq])
                  have sourceEvidence :=
                    inputEvidence.candidate_eq candidateEq
                  rcases sourceEvidence with
                    ⟨sourcePlan, success, relation⟩
                  simp only [Option.some.injEq] at success
                  subst sourcePlan
                  let entriesPlan := TokenPlan.commaSeparated entryPlans
                  let selectionPlan := TokenPlan.enclose
                    (RuleReduction.between file openBrace.span
                      closeBrace.span ()).span
                    (TokenPlan.concat [
                      TokenPlan.plain (.symbol .leftBrace),
                      entriesPlan,
                      TokenPlan.plain (.symbol .rightBrace)])
                  have afterSelection :=
                    relation.concatBookendsToEnclosedPlain
                      (before := [
                        TokenPlan.exact (.hardKeyword .importKw)
                          importKw.span,
                        referencePlan,
                        TokenPlan.exact (.symbol .dot) dot.span])
                      (after := [hidingPlan,
                        TokenPlan.exact (.symbol .semicolon)
                          semicolon.span])
                      openBrace.span_validFor closeBrace.span_validFor
                  have afterImport := afterSelection.concatExactToPlain
                    (before := [])
                    (after := [referencePlan,
                      TokenPlan.exact (.symbol .dot) dot.span,
                      selectionPlan, hidingPlan,
                      TokenPlan.exact (.symbol .semicolon)
                        semicolon.span])
                  have afterDot := afterImport.concatExactToPlain
                    (before := [
                      TokenPlan.plain (.hardKeyword .importKw),
                      referencePlan])
                    (after := [selectionPlan, hidingPlan,
                      TokenPlan.exact (.symbol .semicolon)
                        semicolon.span])
                  have innerRelation := afterDot.concatExactToPlain
                    (before := [
                      TokenPlan.plain (.hardKeyword .importKw),
                      referencePlan,
                      TokenPlan.plain (.symbol .dot),
                      selectionPlan, hidingPlan])
                    (after := [])
                  let inner := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .importKw),
                    referencePlan,
                    TokenPlan.plain (.symbol .dot),
                    selectionPlan,
                    hidingPlan,
                    TokenPlan.plain (.symbol .semicolon)]
                  have innerAnchored : inner.WellAnchored := by
                    exact TokenPlan.WellAnchored.concatPlainBookended
                      (.hardKeyword .importKw) (.symbol .semicolon)
                      [referencePlan, TokenPlan.plain (.symbol .dot),
                        selectionPlan, hidingPlan]
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some innerRelation)
                    (fun plan planEq => by
                      simp only [Option.some.injEq] at planEq
                      subst plan
                      exact innerAnchored)
                    witness.consumed
                  have entriesOutputEq :
                      entries.mapM importSelectorEntryPlan? =
                        some entryPlans := by
                    rw [← importEntryRulePlans_eq]
                    exact entriesEq
                  have hidingOutputEq :
                      importHidingOutput hidingValue = some hidingPlan := by
                    exact (importHidingCandidate_eq_output
                      hidingValue).symm.trans hidingEq
                  apply enclosed.candidate_eq
                  simp only [ruleTokenPlan?, importDeclPlan?, sourceLoc,
                    referenceEq]
                  unfold importSelectionPlan?
                  rwDeclarationPlansMapM
                  simp only [RuleReduction.between]
                  rw [entriesOutputEq]
                  unfoldOptionalPlanCore
                  cases hidingValue with
                  | none =>
                      simp [importHidingOutput] at hidingOutputEq
                      subst hidingPlan
                      simp [entriesPlan, selectionPlan, inner,
                        RuleReduction.between, TokenPlan.concat_cons,
                        TokenPlan.append_assoc]
                  | some clause =>
                      have clauseEq : hidingClausePlan? clause =
                          some hidingPlan := by
                        simpa [importHidingOutput] using hidingOutputEq
                      simp [clauseEq, entriesPlan, selectionPlan, inner,
                        RuleReduction.between, TokenPlan.concat_cons,
                        TokenPlan.append_assoc]

/-- Every export declaration preserves its local or remote selection, optional
alias, wildcard marker, delimiters, and enclosing span. -/
theorem exportDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .exportDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | exportDeclModule origin finish exportKw reference semicolon witness =>
      change EbnfValue file tokens (.choice exportDeclBranches) at input
      rw [← inputEq] at inputEvidence
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none := by
            rw [inputEq]
            exact (exportDeclModuleInput_tokenPlan?
              exportKw reference semicolon).trans (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .exportKw) exportKw.span,
                  referencePlan,
                  .exact (.symbol .semicolon) semicolon.span]) := by
            rw [inputEq]
            exact (exportDeclModuleInput_tokenPlan?
              exportKw reference semicolon).trans (by simp [referenceEq])
          have sourceEvidence := inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst sourcePlan
          have afterKeyword := relation.concatExactToPlain
            (before := [])
            (after := [referencePlan,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterKeyword.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .exportKw),
              referencePlan]) (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .exportKw),
            referencePlan,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .exportKw) (.symbol .semicolon)
              [referencePlan]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan planEq => by
              simp only [Option.some.injEq] at planEq
              subst plan
              exact innerAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, exportDeclPlan?, sourceLoc,
            referenceEq]
          unfoldOptionalAliasPlanCore
          simp [inner, TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | exportDeclAliased origin finish exportKw reference asKw name semicolon
      nameProjects witness =>
      change EbnfValue file tokens (.choice exportDeclBranches) at input
      rw [← inputEq] at inputEvidence
      let nameLoc := RuleReduction.terminalLoc name.matched name.parsed
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none := by
            rw [inputEq]
            exact (exportDeclAliasedInput_tokenPlan?
              exportKw reference asKw name semicolon nameProjects).trans
                (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .exportKw) exportKw.span,
                  referencePlan,
                  .exact (.hardKeyword .asKw) asKw.span,
                  identifierPlan nameLoc,
                  .exact (.symbol .semicolon) semicolon.span]) := by
            rw [inputEq]
            exact (exportDeclAliasedInput_tokenPlan?
              exportKw reference asKw name semicolon nameProjects).trans
                (by simp [referenceEq, nameLoc])
          have sourceEvidence := inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst sourcePlan
          have afterExport := relation.concatExactToPlain
            (before := [])
            (after := [referencePlan,
              TokenPlan.exact (.hardKeyword .asKw) asKw.span,
              identifierPlan nameLoc,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have afterAs := afterExport.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .exportKw),
              referencePlan])
            (after := [identifierPlan nameLoc,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterAs.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .exportKw),
              referencePlan, TokenPlan.plain (.hardKeyword .asKw),
              identifierPlan nameLoc])
            (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .exportKw),
            referencePlan,
            TokenPlan.plain (.hardKeyword .asKw),
            identifierPlan nameLoc,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .exportKw) (.symbol .semicolon)
              [referencePlan, TokenPlan.plain (.hardKeyword .asKw),
                identifierPlan nameLoc]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan planEq => by
              simp only [Option.some.injEq] at planEq
              subst plan
              exact innerAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, exportDeclPlan?, sourceLoc,
            referenceEq]
          unfoldOptionalAliasPlanCore
          simp [nameLoc, inner, TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | exportDeclLocal origin finish exportKw openBrace entries closeBrace
      semicolon witness =>
      change EbnfValue file tokens (.choice exportDeclBranches) at input
      rw [← inputEq] at inputEvidence
      have rawCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let entryPlans ←
              entries.mapM (ruleTokenPlan? .localExportEntry)
            pure (TokenPlan.concat [
              .exact (.hardKeyword .exportKw) exportKw.span,
              .exact (.symbol .leftBrace) openBrace.span,
              .commaSeparated entryPlans,
              .exact (.symbol .rightBrace) closeBrace.span,
              .exact (.symbol .semicolon) semicolon.span])) := by
        rw [inputEq]
        exact exportDeclLocalInput_tokenPlan?
          exportKw openBrace entries closeBrace semicolon
      cases entriesEq :
          entries.mapM (ruleTokenPlan? .localExportEntry) with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none :=
            rawCandidateEq.trans (by simp [entriesEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some entryPlans =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .exportKw) exportKw.span,
                  .exact (.symbol .leftBrace) openBrace.span,
                  .commaSeparated entryPlans,
                  .exact (.symbol .rightBrace) closeBrace.span,
                  .exact (.symbol .semicolon) semicolon.span]) :=
            rawCandidateEq.trans (by simp [entriesEq])
          have sourceEvidence := inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst sourcePlan
          let entriesPlan := TokenPlan.commaSeparated entryPlans
          let selectionPlan := TokenPlan.enclose
            (RuleReduction.between file openBrace.span closeBrace.span ()).span
            (TokenPlan.concat [
              TokenPlan.plain (.symbol .leftBrace),
              entriesPlan,
              TokenPlan.plain (.symbol .rightBrace)])
          have afterSelection :=
            relation.concatBookendsToEnclosedPlain
              (before := [TokenPlan.exact (.hardKeyword .exportKw)
                exportKw.span])
              (after := [TokenPlan.exact (.symbol .semicolon)
                semicolon.span])
              openBrace.span_validFor closeBrace.span_validFor
          have afterExport := afterSelection.concatExactToPlain
            (before := [])
            (after := [selectionPlan,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterExport.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .exportKw),
              selectionPlan])
            (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .exportKw),
            selectionPlan,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .exportKw) (.symbol .semicolon)
              [selectionPlan]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan planEq => by
              simp only [Option.some.injEq] at planEq
              subst plan
              exact innerAnchored)
            witness.consumed
          have entriesOutputEq :
              entries.mapM localExportEntryPlan? = some entryPlans := by
            rw [← localExportRulePlans_eq]
            exact entriesEq
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, exportDeclPlan?, sourceLoc]
          unfold localExportListPlan?
          rwDeclarationPlansMapM
          simp only [RuleReduction.between]
          rw [entriesOutputEq]
          simp [entriesPlan, selectionPlan, inner,
            RuleReduction.between, TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | exportDeclWildcard origin finish exportKw reference dot star semicolon
      starMarker witness =>
      change EbnfValue file tokens (.choice exportDeclBranches) at input
      rw [← inputEq] at inputEvidence
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none := by
            rw [inputEq]
            exact (exportDeclWildcardInput_tokenPlan?
              exportKw reference dot star semicolon).trans
                (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout =
                some (TokenPlan.concat [
                  .exact (.hardKeyword .exportKw) exportKw.span,
                  referencePlan,
                  .exact (.symbol .dot) dot.span,
                  .exact (.symbol .star) star.span,
                  .exact (.symbol .semicolon) semicolon.span]) := by
            rw [inputEq]
            exact (exportDeclWildcardInput_tokenPlan?
              exportKw reference dot star semicolon).trans
                (by simp [referenceEq])
          have sourceEvidence := inputEvidence.candidate_eq candidateEq
          rcases sourceEvidence with ⟨sourcePlan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst sourcePlan
          let selectionPlan := TokenPlan.enclose
            (RuleReduction.between file dot.span star.span ()).span
            (TokenPlan.concat [
              TokenPlan.plain (.symbol .dot),
              TokenPlan.empty,
              TokenPlan.exact (.symbol .star) star.span])
          have afterSelection :=
            relation.concatBookendsToEnclosedPlainExact
              (before := [
                TokenPlan.exact (.hardKeyword .exportKw) exportKw.span,
                referencePlan])
              (after := [TokenPlan.exact (.symbol .semicolon)
                semicolon.span])
              (middle := TokenPlan.empty)
              dot.span_validFor star.span_validFor
          have afterExport := afterSelection.concatExactToPlain
            (before := [])
            (after := [referencePlan, selectionPlan,
              TokenPlan.exact (.symbol .semicolon) semicolon.span])
          have innerRelation := afterExport.concatExactToPlain
            (before := [TokenPlan.plain (.hardKeyword .exportKw),
              referencePlan, selectionPlan])
            (after := [])
          let inner := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .exportKw),
            referencePlan,
            selectionPlan,
            TokenPlan.plain (.symbol .semicolon)]
          have innerAnchored : inner.WellAnchored := by
            exact TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .exportKw) (.symbol .semicolon)
              [referencePlan, selectionPlan]
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun plan planEq => by
              simp only [Option.some.injEq] at planEq
              subst plan
              exact innerAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          simp only [ruleTokenPlan?, exportDeclPlan?, sourceLoc,
            referenceEq]
          unfoldRemoteSelectionAfterReferenceCore
          unfold remoteExportSelectionPlan?
          unfoldMarkerPlanCore
          simp [selectionPlan, inner, RuleReduction.between,
            RuleReduction.marker, RuleReduction.terminalLoc,
            TokenPlan.concat_cons,
            TokenPlan.append_assoc]
  | exportDeclBraced origin finish exportKw reference dot openBrace entries
      closeBrace semicolon witness =>
      change EbnfValue file tokens (.choice exportDeclBranches) at input
      rw [← inputEq] at inputEvidence
      have rawCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let referencePlan ← moduleReferencePlan? reference
            let entryPlans ←
              entries.mapM (ruleTokenPlan? .remoteExportEntry)
            pure (TokenPlan.concat [
              .exact (.hardKeyword .exportKw) exportKw.span,
              referencePlan,
              .exact (.symbol .dot) dot.span,
              .exact (.symbol .leftBrace) openBrace.span,
              .commaSeparated entryPlans,
              .exact (.symbol .rightBrace) closeBrace.span,
              .exact (.symbol .semicolon) semicolon.span])) := by
        rw [inputEq]
        exact exportDeclBracedInput_tokenPlan?
          exportKw reference dot openBrace entries closeBrace semicolon
      cases referenceEq : moduleReferencePlan? reference with
      | none =>
          have candidateEq :
              input.tokenPlan? sourceRuleTokenPlanLayout = none :=
            rawCandidateEq.trans (by simp [referenceEq])
          have noneEvidence := inputEvidence.candidate_eq candidateEq
          rcases noneEvidence with ⟨plan, success, relation⟩
          contradiction
      | some referencePlan =>
          cases entriesEq :
              entries.mapM (ruleTokenPlan? .remoteExportEntry) with
          | none =>
              have candidateEq :
                  input.tokenPlan? sourceRuleTokenPlanLayout = none :=
                rawCandidateEq.trans (by simp [referenceEq, entriesEq])
              have noneEvidence := inputEvidence.candidate_eq candidateEq
              rcases noneEvidence with ⟨plan, success, relation⟩
              contradiction
          | some entryPlans =>
              have candidateEq :
                  input.tokenPlan? sourceRuleTokenPlanLayout =
                    some (TokenPlan.concat [
                      .exact (.hardKeyword .exportKw) exportKw.span,
                      referencePlan,
                      .exact (.symbol .dot) dot.span,
                      .exact (.symbol .leftBrace) openBrace.span,
                      .commaSeparated entryPlans,
                      .exact (.symbol .rightBrace) closeBrace.span,
                      .exact (.symbol .semicolon) semicolon.span]) :=
                rawCandidateEq.trans (by simp [referenceEq, entriesEq])
              have sourceEvidence := inputEvidence.candidate_eq candidateEq
              rcases sourceEvidence with
                ⟨sourcePlan, success, relation⟩
              simp only [Option.some.injEq] at success
              subst sourcePlan
              let entriesPlan := TokenPlan.commaSeparated entryPlans
              let selectionPlan := TokenPlan.enclose
                (RuleReduction.between file openBrace.span
                  closeBrace.span ()).span
                (TokenPlan.concat [
                  TokenPlan.plain (.symbol .leftBrace),
                  entriesPlan,
                  TokenPlan.plain (.symbol .rightBrace)])
              have afterSelection :=
                relation.concatBookendsToEnclosedPlain
                  (before := [
                    TokenPlan.exact (.hardKeyword .exportKw)
                      exportKw.span,
                    referencePlan,
                    TokenPlan.exact (.symbol .dot) dot.span])
                  (after := [TokenPlan.exact (.symbol .semicolon)
                    semicolon.span])
                  openBrace.span_validFor closeBrace.span_validFor
              have afterExport := afterSelection.concatExactToPlain
                (before := [])
                (after := [referencePlan,
                  TokenPlan.exact (.symbol .dot) dot.span,
                  selectionPlan,
                  TokenPlan.exact (.symbol .semicolon) semicolon.span])
              have afterDot := afterExport.concatExactToPlain
                (before := [TokenPlan.plain (.hardKeyword .exportKw),
                  referencePlan])
                (after := [selectionPlan,
                  TokenPlan.exact (.symbol .semicolon) semicolon.span])
              have innerRelation := afterDot.concatExactToPlain
                (before := [TokenPlan.plain (.hardKeyword .exportKw),
                  referencePlan, TokenPlan.plain (.symbol .dot),
                  selectionPlan])
                (after := [])
              let inner := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .exportKw),
                referencePlan,
                TokenPlan.plain (.symbol .dot),
                selectionPlan,
                TokenPlan.plain (.symbol .semicolon)]
              have innerAnchored : inner.WellAnchored := by
                exact TokenPlan.WellAnchored.concatPlainBookended
                  (.hardKeyword .exportKw) (.symbol .semicolon)
                  [referencePlan, TokenPlan.plain (.symbol .dot),
                    selectionPlan]
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan planEq => by
                  simp only [Option.some.injEq] at planEq
                  subst plan
                  exact innerAnchored)
                witness.consumed
              have entriesOutputEq :
                  entries.mapM remoteExportEntryPlan? =
                    some entryPlans := by
                rw [← remoteExportRulePlans_eq]
                exact entriesEq
              apply enclosed.candidate_eq
              simp only [ruleTokenPlan?, exportDeclPlan?, sourceLoc,
                referenceEq]
              unfoldRemoteSelectionAfterReferenceCore
              simp only [RuleReduction.between]
              unfold remoteExportSelectionPlan?
              simp only [RuleReduction.between]
              rwDeclarationPlansMapM
              rw [entriesOutputEq]
              simp [entriesPlan, selectionPlan, inner,
                RuleReduction.between, TokenPlan.concat_cons,
                TokenPlan.append_assoc]

end Solcore.Surface.Multi
