package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class PreIncrementAssignment extends NonTerminatingTranslation {
    
    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public PreIncrementAssignment(MethodVisitor mv, ProgVarHelper pvHelper) {
        super(mv, pvHelper);
    }

    @Override
    public void doCompile(TacletApp app) {
        LocationVariable pv1 = (LocationVariable) getTacletAppInstValue(
                app, "#lhs0");
        LocationVariable pv2 = (LocationVariable) getTacletAppInstValue(
                app, "#lhs1");

        if (pv1.getKeYJavaType().getJavaType().toString().equals("int")) {

            mv().visitIincInsn(pvHelper().progVarNr(pv2), 1);
            mv().visitVarInsn(ILOAD, pvHelper().progVarNr(pv2));
            mv().visitVarInsn(ISTORE, pvHelper().progVarNr(pv1));

        } else {
            onlyIntegerTypesError(pv1.getKeYJavaType());
        }
    }

}
