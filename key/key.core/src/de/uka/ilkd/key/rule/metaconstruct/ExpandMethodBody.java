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

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableArray;

import java.util.HashMap;
import java.util.LinkedHashMap;

/**
 * Replaces the MethodBodyStatement shortcut with the full body, performs prefix
 * adjustments in the body (execution context).
 */
public class ExpandMethodBody extends ProgramTransformer {

    public ExpandMethodBody(SchemaVariable sv) {
        super(new Name("expand-method-body"), (ProgramSV) sv);
    }

    public ExpandMethodBody(Statement mb) {
        super(new Name("expand-method-body"), mb);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        MethodBodyStatement mbs = (MethodBodyStatement) pe;
        // MethodReference mr = mbs.getMethodReference();

        IProgramMethod pm = mbs.getProgramMethod(services);
        // mr.method(services, mbs.getBodySource());

        MethodDeclaration methDecl = pm.getMethodDeclaration();

        StatementBlock result = (StatementBlock) mbs.getBody(services);
        ReferencePrefix newCalled = mbs.getDesignatedContext();
        if (newCalled instanceof TypeReference) {
            // static method
            newCalled = null;
        }

        // removed this again. see bugs #437,#479 -- vladimir
        // result = prettyNewObjectNames(result, methDecl, classContext);

        // at this point all arguments should be program variables
        ImmutableArray<? extends Expression> argsAsParam = mbs.getArguments();

        final HashMap<ProgramVariable, ProgramVariable> map = new LinkedHashMap<>();
        for (int i = 0; i < argsAsParam.size(); i++) {
            IProgramVariable pv = methDecl.getParameterDeclarationAt(i)
                    .getVariableSpecification().getProgramVariable();
            assert pv instanceof ProgramVariable : "Unexpected schematic variable";
            Expression arg = argsAsParam.get(i);
            assert arg instanceof ProgramVariable : "Unexpected schematic variable";
            map.put((ProgramVariable) pv, (ProgramVariable) argsAsParam.get(i));
        }
        ProgVarReplaceVisitor paramRepl = new ProgVarReplaceVisitor(result, map,
            services);
        paramRepl.start();
        result = (StatementBlock) paramRepl.result();

        return new ProgramElement[] { KeYJavaASTFactory.methodFrame(
            mbs.getResultVariable(), KeYJavaASTFactory
                    .executionContext(mbs.getBodySource(), pm, newCalled),
            result, PositionInfo.UNDEFINED) };
    }

}