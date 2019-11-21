// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.abstractexecution.relational.components;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.relational.model.ProgramVariableDeclaration;

/**
 * @author Dominic Steinhoefel
 */
public class StatementLevelJavaErrorParser extends JavaErrorParser {
    private final Set<ProgramVariableDeclaration> progVarDecls = new HashSet<>();
    private String methodLevelContext = "";

    public void setProgVarDecls(Collection<ProgramVariableDeclaration> progVarDecls) {
        this.progVarDecls.clear();
        this.progVarDecls.addAll(progVarDecls);
    }

    public void setMethodLevelContext(final String methodLevelContext) {
        this.methodLevelContext = methodLevelContext;
    }

    protected String createDocument(final String className, final String body) {
        final String newBody = replaceAbstractStatement(replaceAbstractExpression(body));

        final StringBuilder sb = new StringBuilder();

        sb.append("public class ");
        sb.append(className);
        sb.append("{");
        sb.append("public Object method(");
        sb.append(progVarDecls.stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(", ")));
        sb.append(") {");
        sb.append("\n");

        sb.append(newBody);

        sb.append("\n");
        sb.append("return null;}");
        sb.append(methodLevelContext.replaceAll("\n", ""));
        sb.append("}");
        
        return sb.toString();

    }

}
