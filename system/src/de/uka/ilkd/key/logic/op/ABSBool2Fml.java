package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 07.04.13
 * Time: 02:03
 * To change this template use File | Settings | File Templates.
 */
public class ABSBool2Fml extends AbstractTermTransformer {
    protected ABSBool2Fml() {
        super(new Name("#bool2Fml"), 1, Sort.FORMULA);
    }


    @Override
    public Term transform(Term term, SVInstantiations svInst, IServices services) {
        if (term.sub(0).sort() == Sort.FORMULA) {
            return term.sub(0);
        }
        return services.getTermBuilder().equals(term.sub(0), services.getTypeConverter().getBooleanLDT().getTrueTerm());
    }
}
