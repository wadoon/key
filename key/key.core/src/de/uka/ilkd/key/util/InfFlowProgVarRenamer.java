/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.util;

import java.util.HashMap;
import java.util.Map;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.ElementaryUpdate;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.UpdateableOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.VariableNameProposer;


/**
 *
 * @author christoph
 */
public class InfFlowProgVarRenamer extends TermBuilder {
    /** The set of terms on which the renaming should be applied. */
    private final JavaDLTerm[] terms;

    /** Link between program variables / skolem constants and their renamed
     *  counterparts. This map may be pre-initialised.
     */
    private final Map<JavaDLTerm, JavaDLTerm> replaceMap;

    /** The postfix used for renaming, if a program variable / skolem constant
     *  is found which is not yet in the replaceMap.
     */
    private final String postfix;

    /** Goal on which newly created program variables are registered in. */
    private final Goal goalForVariableRegistration;


    public InfFlowProgVarRenamer(JavaDLTerm[] terms,
                                 Map<JavaDLTerm, JavaDLTerm> preInitialisedReplaceMap,
                                 String postfix,
                                 Goal goalForVariableRegistration,
                                 Services services) {
        super(services.getTermFactory(), services);
        this.terms = terms;
        this.postfix = postfix;
        this.goalForVariableRegistration = goalForVariableRegistration;
        if (preInitialisedReplaceMap == null) {
            this.replaceMap = new HashMap<JavaDLTerm, JavaDLTerm>();
        } else {
            this.replaceMap = preInitialisedReplaceMap;
        }

        // the built-in heap symbol has to be handled with care; it is safer
        // not to replace it
        this.replaceMap.put(getBaseHeap(), getBaseHeap());
    }
    

    public InfFlowProgVarRenamer(JavaDLTerm[] terms,
                                 String postfix,
                                 Goal goalForVariableRegistration,
                                 Services services) {
        this(terms, null, postfix, goalForVariableRegistration, services);
    }

    
    public JavaDLTerm[] renameVariablesAndSkolemConstants() {
        JavaDLTerm[] result = new JavaDLTerm[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = renameVariablesAndSkolemConstants(terms[i]);
        }
        return result;
    }


    private JavaDLTerm renameVariablesAndSkolemConstants(JavaDLTerm term) {
        final JavaDLTerm temp = renameFormulasWithoutPrograms(term);
        final Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                restrictToProgramVariables(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap);
    }


    private JavaDLTerm renameFormulasWithoutPrograms(JavaDLTerm term) {
        if (term == null) {
            return null;
        }

        if (!replaceMap.containsKey(term)) {
            renameAndAddToReplaceMap(term);
        }
        return replaceMap.get(term);
    }


    private void renameAndAddToReplaceMap(JavaDLTerm term) {
        if (term.op() instanceof ProgramVariable) {
            renameProgramVariable(term);
        } else if (term.op() instanceof Function &&
                   ((Function) term.op()).isSkolemConstant()) {
            renameSkolemConstant(term);
        } else if (term.op() instanceof ElementaryUpdate) {
            applyRenamingsOnUpdate(term);
        } else {
            applyRenamingsOnSubterms(term);
        }
    }


    private void renameProgramVariable(JavaDLTerm term) {
        assert term.arity() == 0;
        final ProgramVariable pv = (ProgramVariable) term.op();
        final Name newName =
                VariableNameProposer.DEFAULT.getNewName(services,
                                                        new Name(pv.name() +
                                                                 postfix));
        final Operator renamedPv = pv.rename(newName);

        // for the taclet application dialog (which gets the declared
        // program variables in a strange way and not directly from the
        // namespace); adds the renamedPv also to the namespace
        goalForVariableRegistration.addProgramVariable((ProgramVariable)renamedPv);

        final JavaDLTerm pvTerm = label(var((ProgramVariable)renamedPv),
                                  term.getLabels());
        replaceMap.put(term, pvTerm);
    }


    private void renameSkolemConstant(JavaDLTerm term) {
        final Function f = (Function) term.op();
        final Name newName =
                VariableNameProposer.DEFAULT.getNewName(services,
                                                        new Name(f.name() +
                                                                 postfix));
        final Function renamedF = f.rename(newName);
        services.getNamespaces().functions().addSafely(renamedF);
        final JavaDLTerm fTerm =
                label(func(renamedF),
                      term.getLabels());
        replaceMap.put(term, fTerm);
    }


    private void applyRenamingsOnUpdate(JavaDLTerm term) {
        final ElementaryUpdate u = (ElementaryUpdate) term.op();
        final JavaDLTerm lhsTerm = var(u.lhs());
        final JavaDLTerm renamedLhs = renameFormulasWithoutPrograms(lhsTerm);
        final JavaDLTerm[] renamedSubs = renameSubs(term);
        final ElementaryUpdate renamedU =
                ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
        final JavaDLTerm uTerm =
                label(tf().createTerm(renamedU, renamedSubs),
                      term.getLabels());
        replaceMap.put(term, uTerm);
    }


    private void applyRenamingsOnSubterms(JavaDLTerm term) {
        final JavaDLTerm[] renamedSubs = renameSubs(term);
        final JavaDLTerm renamedTerm =
                tf().createTerm(term.op(), renamedSubs,
                                term.boundVars(), term.modalContent(),
                                term.getLabels());
        replaceMap.put(term, renamedTerm);
    }


    private JavaDLTerm[] renameSubs(JavaDLTerm term) {
        JavaDLTerm[] renamedSubs = new JavaDLTerm[term.arity()];
        for (int i = 0; i < renamedSubs.length; i++) {
            renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i));
        }
        return renamedSubs;
    }


    private JavaDLTerm applyRenamingsToPrograms(JavaDLTerm term,
                                          Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {

        if (term != null) {
            final JavaBlock renamedJavaBlock =
                    renameJavaBlock(progVarReplaceMap, term, services);
            final JavaDLTerm[] appliedSubs =
                    applyProgramRenamingsToSubs(term, progVarReplaceMap);

            final JavaDLTerm renamedTerm =
                    tf().createTerm(term.op(), appliedSubs,
                                    term.boundVars(), renamedJavaBlock,
                                    term.getLabels());
            return renamedTerm;
        } else {
            return null;
        }
    }


    private JavaDLTerm[] applyProgramRenamingsToSubs(JavaDLTerm term,
                                               Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {
        JavaDLTerm[] appliedSubs = new JavaDLTerm[term.arity()];
        for (int i = 0; i < appliedSubs.length; i++) {
            appliedSubs[i] = applyRenamingsToPrograms(term.sub(i),
                    progVarReplaceMap);
        }
        return appliedSubs;
    }


    private JavaBlock renameJavaBlock(Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                      JavaDLTerm term, Services services) {
        final ProgVarReplaceVisitor paramRepl =
                new ProgVarReplaceVisitor(term.modalContent().program(), progVarReplaceMap, services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Map<ProgramVariable, ProgramVariable>
                        restrictToProgramVariables(Map<JavaDLTerm, JavaDLTerm> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                new HashMap<ProgramVariable, ProgramVariable>();
        for (final JavaDLTerm t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable) t.op(),
                                      (ProgramVariable) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }
}
