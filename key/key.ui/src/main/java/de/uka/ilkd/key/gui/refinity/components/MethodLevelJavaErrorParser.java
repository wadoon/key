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
package de.uka.ilkd.key.gui.refinity.components;

/**
 * @author Dominic Steinhoefel
 */
public class MethodLevelJavaErrorParser extends JavaErrorParser {
    protected String createDocument(final String className, final String body) {
        final String newBody = replaceAbstractStatement(replaceAbstractExpression(body));

        final StringBuilder sb = new StringBuilder();

        sb.append("public class ");
        sb.append(className);
        sb.append("{\n");

        sb.append(newBody);

        sb.append("\n}");

        return sb.toString();

    }

}
