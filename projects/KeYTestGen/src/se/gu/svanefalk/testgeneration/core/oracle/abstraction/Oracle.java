package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import java.util.Set;

/**
 * Represents a test case oracle - that is, a set of constraints on post-state
 * of a program following the execution of a test case.
 * <p>
 * An Oracle is essentially a FOL formula in conjunctive normal form - it
 * consists of a set of sub-formulas ({@link OracleClause} instances) joined
 * only by conjunction.
 * 
 * @author christopher
 * 
 */
public class Oracle {

    public Oracle(final Set<OracleClause> assertions) {
    }
}
