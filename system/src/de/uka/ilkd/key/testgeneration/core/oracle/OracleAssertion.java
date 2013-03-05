package de.uka.ilkd.key.testgeneration.core.oracle;

import java.util.HashSet;
import java.util.Set;

/**
 * An OracleAssertion is a set of FOL formulas joined by disjunctions.
 * 
 * @author christopher
 * 
 */
public class OracleAssertion {
    
    Set<OracleExpression> expressions= new HashSet<OracleExpression>();

}
