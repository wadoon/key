package de.uka.ilkd.keyabs.rule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class ABSTacletVariableSVCollector extends
        ABSTacletSchemaVariableCollector {
    /**
     * visits term t in post order (
     * {@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)}) and collects
     * all bound schema variables
     * 
     * @param t
     *            the Term to be visited (<code>t</code> must not be
     *            <code>null</code>
     */
    @Override
    public void visit(Term t) {
        for (int j = 0; j < t.arity(); j++) {
            for (int i = 0; i < t.varsBoundHere(j).size(); i++) {
                QuantifiableVariable boundVar = t.varsBoundHere(j).get(i);
                if (boundVar instanceof SchemaVariable) {
                    varList = varList.prepend((SchemaVariable) boundVar);
                }
            }
        }
    }
}
