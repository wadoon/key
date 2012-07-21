// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.visitor.ProgramSVCollector;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRuleWrapper;

/**
 * Collects all schemavariables occurring in the <code>\find, \assumes</code>
 * part or goal description of a taclet. The addrule section is scanned
 * optionally.
 * 
 * Duplicates are not removed because the use of persistent datastructure and up
 * to now we just have a SetAsList-implementaion causing to have O(sqr(n)) if it
 * would used.
 * 
 * For example, {@link de.uka.ilkd.key.rule.TacletApp} uses this class to
 * determine all uninstantiated schemavariables.
 */
public class TacletSchemaVariableCollector extends
        AbstractTacletSchemaVariableCollector {

    public TacletSchemaVariableCollector() {
        super();
    }

    /**
     * collects all SchemVariables that occur in the JavaBlock
     * 
     * @param jb
     *            the JavaBlock where to look for Schemavariables
     * @param vars
     *            the IList<SchemaVariable> where to add the found
     *            SchemaVariables
     * @return the extended list of found schemavariables
     */
    @Override
    protected ImmutableList<SchemaVariable> collectSVInProgram(JavaBlock jb,
            ImmutableList<SchemaVariable> vars) {

        ProgramSVCollector prgSVColl = new ProgramSVCollector(jb.program(),
                vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }

    @Override
    public void visit(Term t) {
        if (t.op() instanceof WhileInvRule) {
            varList = collectSVInProgram(t, varList);
        }
    }

    @Override
    protected ImmutableList<SchemaVariable> collectSVInProgram(Term t,
            ImmutableList<SchemaVariable> vars) {

        ProgramSVCollector prgSVColl = new ProgramSVCollector(
                new WhileInvRuleWrapper(t), vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }

}
