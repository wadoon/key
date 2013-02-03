package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;

/**
 * This parser is used in order to put a Term into Conjunctive Normal Form.
 * <p>
 * Assume that a Literal <i>L</i> is either an atom p or the negation of an atom
 * !p. A Term <i>T</i> is in CNF if it is a conjunction of clauses, where each
 * clause <i>D</i> is a disjunction of literals:
 * 
 * <pre>
 * L ::= p | !p
 * D ::= L | L OR D
 * C ::= D | D AND T
 * </pre>
 * 
 * (Huth and Ryan, <i>Logic in Computer Science</i>, 2nd Ed. Cambridge
 * University press, 2008)
 * 
 * @author christopher
 * 
 */
public class CNFTransformer {

    public Term TermToCNF(Term term) {

        return null;
    }
}