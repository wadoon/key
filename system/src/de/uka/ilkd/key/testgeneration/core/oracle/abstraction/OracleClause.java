package de.uka.ilkd.key.testgeneration.core.oracle.abstraction;

import java.util.Set;

/**
 * An OracleClause is a set of FOL formulas joined by disjunctions.
 * 
 * @author christopher
 * 
 */
public class OracleClause {

    private final Set<OracleBooleanExpression> disjunctions;

    public OracleClause(Set<OracleBooleanExpression> expressions) {

        this.disjunctions = expressions;
    }
}