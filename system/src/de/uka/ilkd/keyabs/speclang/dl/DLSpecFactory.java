package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.keyabs.abs.ABSServices;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 15:47
 * To change this template use File | Settings | File Templates.
 */
public class DLSpecFactory {


    private final ABSServices services;

    public DLSpecFactory(ABSServices services) {
        this.services = services;
    }

    /**
     * Creates a class invariant from a formula and a designated "self".
     */
    public ABSClassInvariant createDLClassInvariant(String name,
                                                     String displayName,
                                                     String typeName,
                                                     Term inv,
                                                     ParsableVariable historyVar,
                                                     ParsableVariable heapVar,
                                                     ParsableVariable selfVar
                                                    )
            throws ProofInputException {

        assert name != null;
        assert typeName != null;

        if (displayName == null) {
            displayName = name;
        }

        assert inv != null;

        return new ABSClassInvariantImpl(name,
                displayName,
                typeName,
                inv, historyVar, heapVar, selfVar);
    }

    public InterfaceInvariant createDLInterfaceInvariant(String name,
                                                         String displayName,
                                                         String typeName,
                                                         Term inv,
                                                         ParsableVariable historyVar)
            throws ProofInputException {

        assert name != null;
        assert typeName != null;

        if (displayName == null) {
            displayName = name;
        }

        assert inv != null;

        final KeYJavaType kjt
                = services.getProgramInfo().getTypeByName(typeName);
        assert kjt != null;

        return new InterfaceInvariantImpl(name,
                displayName,
                kjt,
                inv, historyVar);
    }


}
