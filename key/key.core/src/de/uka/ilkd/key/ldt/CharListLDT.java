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

package de.uka.ilkd.key.ldt;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;


public final class CharListLDT extends LDT {
    
    public static final Name NAME = new Name("CharList");
    
    public static final Name STRINGPOOL_NAME = new Name("strPool");
    public static final Name STRINGCONTENT_NAME = new Name("strContent");
    
    
    //Warning: Some names of char list functions are hardcoded into 
    //         LexPathOrdering and into CharListNotation!
                
    //functions
    private final Function clIndexOfChar;
    private final Function clIndexOfCl;
    private final Function clLastIndexOfChar;
    private final Function clLastIndexOfCl;
    private final Function clReplace;
    private final Function clTranslateInt;
    private final Function clRemoveZeros;
    private final Function clHashCode;

    //predicates
    private final Function clStartsWith;
    private final Function clEndsWith;
    private final Function clContains;


    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public CharListLDT(JavaDLTermServices services) {
	super(NAME, (Sort) services.getNamespaces().sorts().lookup(SeqLDT.NAME));
	clIndexOfChar     = addFunction(services, "clIndexOfChar");
	clIndexOfCl       = addFunction(services, "clIndexOfCl");
	clLastIndexOfChar = addFunction(services, "clLastIndexOfChar");
	clLastIndexOfCl   = addFunction(services, "clLastIndexOfCl");
	clReplace         = addFunction(services, "clReplace");
	clTranslateInt    = addFunction(services, "clTranslateInt");
	clRemoveZeros     = addFunction(services, "clRemoveZeros");
	clHashCode        = addFunction(services, "clHashCode");

	clStartsWith      = addFunction(services, "clStartsWith");
	clEndsWith        = addFunction(services, "clEndsWith");
	clContains        = addFunction(services, "clContains");
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private String translateCharTerm(JavaDLTerm t) {
	char charVal = 0;
	int intVal = 0;
	String result = printlastfirst(t.sub(0)).toString();
	try {
	    intVal = Integer.parseInt(result);
	    charVal = (char) intVal;
	    if (intVal - charVal != 0)
		throw new NumberFormatException(); // overflow!

	} catch (NumberFormatException ex) {
	    throw new ConvertException(result + " is not of type char");
	}
	return ""+charVal;
    }
    

    private StringBuffer printlastfirst(JavaDLTerm t) {
	if (t.op().arity() == 0) {
	    return new StringBuffer();
	} else {
	    return printlastfirst(t.sub(0)).append(t.op().name().toString());
	}
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
        
    
    public Function getClIndexOfChar() {
	return clIndexOfChar;
    }
    
    
    public Function getClIndexOfCl() {
	return clIndexOfCl;
    }
    
    
    public Function getClLastIndexOfChar() {
	return clLastIndexOfChar;
    }
    
   
    public Function getClLastIndexOfCl() {
	return clLastIndexOfCl;
    }
    
    
    public Function getClReplace() {
	return clReplace;
    }
    
    
    public Function getClTranslateInt() {
	return clTranslateInt;
    }
    
    
    public Function getClRemoveZeros() {
	return clRemoveZeros;
    }
   
    
    public Function getClHashCode() {
	return clHashCode;
    }

        
    public Function getClStartsWith() {
	return clStartsWith;
    }
    
    
    public Function getClEndsWith() {
	return clEndsWith;
    }
    
    
    public Function getClContains() {
	return clContains;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 JavaDLTerm[] subs, 
                                 Services services, 
                                 ExecutionContext ec) {
	return false;
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                		 JavaDLTerm left, 
                		 JavaDLTerm right, 
                		 Services services, 
                		 ExecutionContext ec) {
	return false;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	    			 JavaDLTerm sub, 
	    			 JavaDLTermServices services, 
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public JavaDLTerm translateLiteral(Literal lit, Services services) {
	final SeqLDT seqLDT = services.getTheories().getSeqLDT();
    final TermBuilder tb = services.getTermBuilder();
    final JavaDLTerm term_empty = tb.func(seqLDT.getSeqEmpty());

	char[] charArray;
	JavaDLTerm result = term_empty;

	if (lit instanceof StringLiteral) {
	    charArray = ((StringLiteral) lit).getValue().toCharArray();
	} else {
	    return null;
	}

	IntegerLDT intLDT = services.getTheories().getIntegerLDT();
	if (intLDT == null) {
	    throw new IllegalArgumentException(
		    "IntegerLDT is needed for StringLiteral translation");
	}

	for (int i = charArray.length - 2; i >= 1; i--) {
	    JavaDLTerm singleton = tb.seqSingleton(intLDT.translateLiteral(new CharLiteral(charArray[i]), services)); 
	    result = tb.seqConcat(singleton, result);
	}

	return result;
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    
    @Override
    public Expression translateTerm(JavaDLTerm t, ExtList children, Services services) {
	final StringBuffer result = new StringBuffer("");
	JavaDLTerm term = t;
	while (term.op().arity() != 0) {
	    result.append(translateCharTerm(term.sub(0)));
	    term = term.sub(1);
	}
	return new StringLiteral("\"" + result + "\"");
    }
    
    
    @Override
    public final Type getType(JavaDLTerm t) {
	assert false;
	return null;
    }
}