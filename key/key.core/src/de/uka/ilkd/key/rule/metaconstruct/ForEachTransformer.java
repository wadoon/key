// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Arrays;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Special transformer for generating similar programs redundantly in a
 * replacewith part of a taclet. First, pass a sequence of index variables to be
 * instantiated, and then a second sequence of list program variables (of the
 * same length, and the lists by which the variables are instantiated must also
 * have the same length) from which to retrieve the values. The program given as
 * last argument is generated redundantly for each instantiation of the index
 * variables.
 */
public class ForEachTransformer extends ProgramTransformer {

    private final SchemaVariable[] indexVariables;
    private final SchemaVariable[] listVariables;

    /**
     * creates an unwind-loop ProgramTransformer
     *
     * @param loop
     *            the LoopStatement contained by the meta construct
     * @param innerLabel
     *            The inner label SV
     * @param outerLabel
     *            The outer label SV
     */
    public ForEachTransformer(SchemaVariable[] indexVariables,
            SchemaVariable[] listVariables, ProgramElement pattern) {
        super("#foreach", pattern);

        assert indexVariables != null;
        assert listVariables != null;
        assert indexVariables.length == listVariables.length;

        this.indexVariables = indexVariables;
        this.listVariables = listVariables;
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final ProgramElement[] indexVarInsts = Arrays.stream(indexVariables)
                .map(sv -> (ProgramElement) svInst.getInstantiation(sv))
                .collect(Collectors.toList()).toArray(new ProgramElement[0]);
        final ImmutableArray[] listVarInsts = Arrays.stream(listVariables)
                .map(sv -> (ImmutableArray) svInst.getInstantiation(sv))
                .collect(Collectors.toList()).toArray(new ImmutableArray[0]);

        final ProgramElement[] result = new ProgramElement[listVarInsts[0]
                .size()];
        for (int i = 0; i < result.length; i++) {
            ProgramElement currResult = pe;
            for (int j = 0; j < indexVarInsts.length; j++) {
                final ProgramElement placeholder = indexVarInsts[j];
                final ProgramElement substitution = (ProgramElement) listVarInsts[j]
                        .get(i);
                final ProgramElementReplacer replacer = new ProgramElementReplacer(
                    (JavaProgramElement) currResult, services);
                currResult = replacer.replace(placeholder, substitution);
                System.err.println();
            }
            result[i] = currResult;
        }

        return result;
    }
}