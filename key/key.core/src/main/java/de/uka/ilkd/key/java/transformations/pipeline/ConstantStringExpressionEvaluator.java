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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.VoidVisitorWithDefaults;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.transformations.ConstantEvaluator;
import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;

public class ConstantStringExpressionEvaluator extends JavaTransformer {

    public ConstantStringExpressionEvaluator(TransformationPipelineServices services) {
        super(services);
    }


    private void evaluateConstantStringExpressions(Node td) {
        td.accept(new VoidVisitorWithDefaults<>() {
            @Override
            public void defaultAction(Node n, Object arg) {
                if (n instanceof Expression) {
                    ConstantEvaluator cee = services.getConstantEvaluator();
                    Type expType = services.getType((Expression) n);
                    if (!(pe instanceof NullLiteral) && expType != null && expType.getFullName().equals("java.lang.String")) {
                        boolean isCTC = false;
                        try {
                            isCTC = cee.isCompileTimeConstant((Expression) pe, res);
                        } catch (java.lang.ArithmeticException t) {
                            //
                        }
                        if (isCTC && res.getTypeCode() == ConstantEvaluator.STRING_TYPE) {
                            n.replace(new StringLiteralExpr(evaluated));
                            continue;
                        }
                    }
                }
            }
        }, null);
    }

    @Override
    protected void apply(TypeDeclaration<?> td) {
        evaluateConstantStringExpressions(td);
    }
}