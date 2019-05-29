// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates a {@link SchemaVariable} for an
 * {@link AbstractPlaceholderStatement} with a new abstract program.
 *
 * @author Dominic Steinhoefel
 */
public class FreshAbstractProgramCondition implements VariableCondition {
    private final ProgramSV abstractProgSV;

    public FreshAbstractProgramCondition(ProgramSV abstractProgSV) {
        this.abstractProgSV = abstractProgSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(abstractProgSV)) {
            return matchCond;
        }

        final Namespace<AbstractPlaceholderStatement> namespace = services
                .getNamespaces().abstractProgramSymbols();
        final String basename = "P_";

        Name name;
        int cnt = 0;
        do {
            name = new Name(basename + cnt);
            cnt++;
        } while (namespace.lookup(name) != null);

        final AbstractPlaceholderStatement resultInst = //
                new AbstractPlaceholderStatement(name.toString());

        namespace.add(resultInst);

        return matchCond.setInstantiations(
            svInst.add(abstractProgSV, resultInst, services));
    }

}
