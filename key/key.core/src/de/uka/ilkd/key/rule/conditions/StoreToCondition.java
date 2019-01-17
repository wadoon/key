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

package de.uka.ilkd.key.rule.conditions;

import java.util.Map;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * A little "hack-ish" variable condition storing a term/formula to a
 * {@link SchemaVariable}. During application, it is all schema variables of the
 * term/formula are replaced by already existing instantiations.
 *
 * @author Dominic Steinhoefel
 */
public class StoreToCondition implements VariableCondition {
    private final SchemaVariable targetSV;
    private final Term schematicTermToStore;

    public StoreToCondition(SchemaVariable targetSV,
            Term schematicTermToStore) {
        this.targetSV = targetSV;
        this.schematicTermToStore = schematicTermToStore;
    }

    @Override
    public MatchConditions check(SchemaVariable schemaVar,
            SVSubstitute instCandidate, MatchConditions matchCond,
            Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(targetSV) != null) {
            return matchCond;
        }

        final OpCollector opColl = new OpCollector();
        schematicTermToStore.execPostOrder(opColl);

        if (opColl.ops().stream().filter(op -> op instanceof SchemaVariable)
                .map(SchemaVariable.class::cast)
                .anyMatch(sv -> svInst.getInstantiation(sv) == null)) {
            // Obviously, there are some uninstantiated schema variables
            return null;
        }

        final Map<SchemaVariable, SVSubstitute> replMap = opColl.ops().stream()
                .filter(op -> op instanceof SchemaVariable)
                .map(SchemaVariable.class::cast)
                .collect(Collectors.toMap(sv -> sv,
                        sv -> (SVSubstitute) svInst.getInstantiation(sv)));

        final Term concreteTermToStore = //
                replaceSVsInTerm(schematicTermToStore, replMap, services);

        return matchCond.setInstantiations(
                svInst.add(targetSV, concreteTermToStore, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\storeResultVarIn(%s))", targetSV);
    }

    private static Term replaceSVsInTerm(final Term term,
            final Map<SchemaVariable, SVSubstitute> replMap,
            Services services) {
        if (term.op() instanceof SchemaVariable) {
            final SVSubstitute replacement = replMap.get(term.op());

            if (replacement instanceof Term) {
                return replaceSVsInTerm((Term) replacement, replMap, services);
            }
            else if (replacement instanceof Operator) {
                return replaceSVsInTerm(services.getTermFactory().createTerm(
                        (Operator) replacement, term.subs(), term.boundVars(),
                        term.javaBlock(), term.getLabels()), replMap, services);
            }
        }

        return services.getTermFactory().createTerm(//
                term.op(),
                new ImmutableArray<>(term.subs().stream()
                        .map(sub -> replaceSVsInTerm(sub, replMap, services))
                        .collect(Collectors.toList())),
                term.boundVars(), term.javaBlock(), term.getLabels());
    }
}
