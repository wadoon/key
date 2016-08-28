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

package org.key_project.common.core.parser;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.key_project.common.core.parser.KeYCommonRuleParser.TacletContext;
import org.key_project.common.core.parser.exceptions.ProofInputException;

import junit.framework.TestCase;

/**
 * This parser tests just the grammar (i.e., syntax) it does not 
 * perform any semantic tests.
 * @author Richard Bubel
 */
public class TestRuleParser extends TestCase {

    public TestRuleParser(String name) {
        super(name);
    }

    private TacletContext parseRule(String inputStr) {
        // Create the lexer
        KeYCommonLexer lexer = new KeYCommonLexer(new ANTLRInputStream(inputStr));

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        KeYCommonRuleParser parser = new KeYCommonRuleParser(tokens);

        // For testing: bail at error
        parser.setErrorHandler(new BailErrorStrategy());

        // Traverse the parse tree
        try {
            return parser.taclet();
        }
        catch (Exception e) {
            throw new ProofInputException(e.getMessage(), e);
        }
    }
    
    public void testSimpleTaclet() {
        TacletContext result = parseRule("andLeft { \\find ( A & B ==> ) \\replacewith (A, B ==>)  }");        
        assertEquals("andLeft", result.name.getText());    
        // needs to be extended
    }
}
