package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.op.DLQuantifiableVariable;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public interface QuantifiableVariable extends Operator, ParsableVariable, DLQuantifiableVariable<Sort, Term> {

}
