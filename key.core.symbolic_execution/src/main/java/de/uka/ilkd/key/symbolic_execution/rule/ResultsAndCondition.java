package de.uka.ilkd.key.symbolic_execution.rule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

import java.util.Set;

/**
 * The return value of a side proof.
 *
 * @param result     a term representing the result (first formula of succedent)
 * @param conditions formulas of the antecedent
 * @param node       the final node of the side proof
 */
public record ResultsAndCondition(Term result, Set<Term> conditions, Node node) {
}
