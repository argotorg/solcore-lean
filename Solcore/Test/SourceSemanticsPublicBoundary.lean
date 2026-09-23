import Solcore.SourceSemantics

set_option autoImplicit false

namespace Tests

example := @Solcore.SourceSemantics.Context
example := @Solcore.SourceSemantics.Context.ofSignatures
example := @Solcore.SourceSemantics.Context.withLocal
example := @Solcore.SourceSemantics.Context.withAssumption
example := @Solcore.SourceSemantics.Context.LocalLookup
example := @Solcore.SourceSemantics.Context.HasAssumption

example := @Solcore.SourceSemantics.ContainsNode
example := @Solcore.SourceSemantics.ContainsExpression
example := @Solcore.SourceSemantics.ContainsStatement
example := @Solcore.SourceSemantics.NodeOccurrencesUnique
example := @Solcore.SourceSemantics.OccurrenceGraphWellFormed
example := @Solcore.SourceSemantics.lookupExpression?_sound
example := @Solcore.SourceSemantics.lookupExpression?_complete

example := @Solcore.SourceSemantics.ExactSubstitution
example := @Solcore.SourceSemantics.SchemeInstantiates
example := @Solcore.SourceSemantics.ParameterSubstitution.Exact
example := @Solcore.SourceSemantics.DeclarationInstantiation.Valid
example := @Solcore.SourceSemantics.DataConstructorInstantiation.Valid

example := @Solcore.SourceSemantics.Forall₂
example := @Solcore.SourceSemantics.implRuleVariables
example := @Solcore.SourceSemantics.implRuleParameters
example := @Solcore.SourceSemantics.ImplSubstitution
example := @Solcore.SourceSemantics.ImplSubstitution.ExactFor
example := @Solcore.SourceSemantics.ImplHeadInstantiates
example := @Solcore.SourceSemantics.TraitEvidence
example := @Solcore.SourceSemantics.EvidenceValid
example := @Solcore.SourceSemantics.Entails
example := @Solcore.SourceSemantics.EvidenceValid.evidence_goal_eq
example := @Solcore.SourceSemantics.PredicateEvidenceRepresents
example := @Solcore.SourceSemantics.RetainedEvidenceValid

example := @Solcore.SourceSemantics.ReferenceHasRawType
example := @Solcore.SourceSemantics.ReferenceHasRawType.local_iff
example := @Solcore.SourceSemantics.ReferenceExpressionHasRawType
example := @Solcore.SourceSemantics.SolvedRequirementValid
example := @Solcore.SourceSemantics.SolvedRequirementsValid

end Tests
