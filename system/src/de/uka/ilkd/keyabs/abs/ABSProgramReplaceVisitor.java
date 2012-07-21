// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.IProgramReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.Debug;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used to
 * transform a program according to the given SVInstantiations.
 */
public class ABSProgramReplaceVisitor extends ABSModificationVisitor implements
        IProgramReplaceVisitor {

    private SVInstantiations svinsts;

    private boolean allowPartialReplacement;

    private ABSServices services;

    /**
     * create the ProgramReplaceVisitor
     * 
     * @param root
     *            the ProgramElement where to begin
     */
    public ABSProgramReplaceVisitor(ProgramElement root, ABSServices services,
            SVInstantiations svi, boolean allowPartialReplacement) {
        super(root);
        this.services = services;
        svinsts = svi;
        this.allowPartialReplacement = allowPartialReplacement;
    }

    /**
     * the action that is performed just before leaving the node the last time
     */
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.java.visitor.IProgramReplaceVisitor#start()
     */
    @Override
    public void start() {
        walk(root());
    }

    public void performActionOnSchemaVariable(SchemaVariable sv) {
        final Object inst = svinsts.getInstantiation(sv);
        if (inst instanceof ProgramElement) {
            Debug.out("ProgramReplace SV:", sv);
            Debug.out("ProgramReplace:", inst);
            pushChanged((ProgramElement) inst);
        } else if (inst instanceof ImmutableArray/* <ProgramElement> */) {
            final ImmutableArray<ProgramElement> instArray = (ImmutableArray<ProgramElement>) inst;
            // the assertion ensures the intended instanceof check from above
            assert instArray.size() == 0
                    || instArray.last() instanceof ProgramElement;
            for (ProgramElement pe : instArray) {
                pushChanged(pe);
            }
        } else if (inst instanceof Term
                && ((Term) inst).op() instanceof ProgramInLogic) {
            pushChanged(services.getTypeConverter().convertToProgramElement(
                    (Term) inst));
        } else {
            if (inst == null && allowPartialReplacement
                    && sv instanceof SourceElement) {
                push((ProgramElement) sv);
                return;
            }
            Debug.fail("programreplacevisitor: Instantiation missing "
                    + "for schema variable ", sv);
        }
    }

    @Override
    public void performActionOnProgramMetaConstruct(ProgramTransformer<ABSServices> x) {
        IProgramReplaceVisitor trans = new ABSProgramReplaceVisitor(x.body(),
                services, svinsts, allowPartialReplacement);
        trans.start();
        ProgramElement localresult = trans.result();
        localresult = x.transform(localresult, services, svinsts);
        pushChanged(localresult);
    }

    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
        throw new RuntimeException(getClass() + ": Implementaion missing");
    }
}
