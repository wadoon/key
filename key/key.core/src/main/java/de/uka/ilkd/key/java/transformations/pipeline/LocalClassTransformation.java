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

package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.validator.ProblemReporter;
import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.java.transformations.pipeline.ImplicitFieldAdder;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;

import java.util.List;

/**
 * Local and anonymous classes may access variables from the creating context
 * if they are declared final and initialised.
 * <p>
 * This transformation searches for such final variables and replaces them by
 * an implicit variable.
 * <p>
 * Additionally a pseudo name is assigned to anonymous classes to allow to
 * access them despite all.
 *
 * @author engelc
 */
public class LocalClassTransformation extends JavaTransformer {

    public LocalClassTransformation(TransformationPipelineServices services) {
        super(services);
    }

    protected void apply(TypeDeclaration<?> td) {
        List<Variable> outerVars = getLocalClass2FinalVar().get(td);
        CrossReferenceSourceInfo si = services.getCrossReferenceSourceInfo();

        if (outerVars != null) {
            for (final Variable v : outerVars) {
                for (final VariableReference vr : si.getReferences(v)) {
                    if (si.getContainingReferenceType(vr) !=
                            si.getContainingReferenceType((Node) v)) {
                        FieldReference fr = new FieldReference(new ThisReference(),
                                new ImplicitIdentifier(ImplicitFieldAdder.FINAL_VAR_PREFIX +
                                        v.getName()));
                        vr.getParentNode().get().replaceChild(vr, fr);
                        td.makeAllParentRolesValid();
                    }
                }
            }
        }
    }

}