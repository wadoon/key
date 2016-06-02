package org.key_project.common.core.logic.op;


import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Sort;

/**
 * Standard first-order substitution operator, resolving clashes but not
 * preventing (usually unsound) substitution of non-rigid terms across modal
 * operators. Currently, only the subclass <code>WarySubstOp</code> is used
 * and accessible through the key parser.
 */
public abstract class DLSubstOp<S extends Sort> extends DLAbstractOperator {
    
    protected DLSubstOp(Name name) {
    super(name, 2, new Boolean[]{false, true}, true);
    }
        
}