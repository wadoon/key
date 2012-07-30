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
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.IProgramReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

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


    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.java.visitor.IProgramReplaceVisitor#start()
     */
    @Override
    public void start() {
        stack.push(new ExtList());              
        walk(root());
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable sv) {
        final Object inst = svinsts.getInstantiation(sv);
        if (inst instanceof ProgramElement) {
            System.out.println(sv + " --> " + inst);
            
            addNewChild((ProgramElement) inst);
        } else if (inst instanceof ImmutableArray/* <ProgramElement> */) {
            final ImmutableArray<ProgramElement> instArray = (ImmutableArray<ProgramElement>) inst;
            // the assertion ensures the intended instanceof check from above
            assert instArray.size() == 0
                    || instArray.last() instanceof ProgramElement;
            addChildren(instArray);
            changed();
        } else if (inst instanceof Term
                && ((Term) inst).op() instanceof ProgramInLogic) {
            addNewChild(services.getTypeConverter().convertToProgramElement(
                    (Term) inst));
        } else {
            if (inst == null && allowPartialReplacement
                    && sv instanceof SourceElement) {
                unchangedProgramElementAction((ProgramElement) sv);
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
        addNewChild(localresult);
    }
}
