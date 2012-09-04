// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashMap;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaDLTermBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.metaconstruct.AddCast;
import de.uka.ilkd.key.rule.metaconstruct.ArrayBaseInstanceOf;
import de.uka.ilkd.key.rule.metaconstruct.ConstantValue;
import de.uka.ilkd.key.rule.metaconstruct.EnhancedForInvRule;
import de.uka.ilkd.key.rule.metaconstruct.EnumConstantValue;
import de.uka.ilkd.key.rule.metaconstruct.ExpandQueriesMetaConstruct;
import de.uka.ilkd.key.rule.metaconstruct.IntroAtPreDefsOp;
import de.uka.ilkd.key.rule.metaconstruct.MemberPVToField;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.metaconstruct.arith.DivideLCRMonomials;
import de.uka.ilkd.key.rule.metaconstruct.arith.DivideMonomials;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaAdd;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaDiv;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaEqual;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaGeq;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaGreater;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntAnd;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntOr;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntShiftLeft;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntShiftRight;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntUnsignedShiftRight;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaIntXor;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongAnd;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongOr;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongShiftLeft;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongShiftRight;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongUnsignedShiftRight;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaJavaLongXor;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaLeq;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaLess;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaMul;
import de.uka.ilkd.key.rule.metaconstruct.arith.MetaSub;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.keyabs.rule.metaconstruct.GetThisReference;
import de.uka.ilkd.keyabs.rule.metaconstruct.MethodArgsToSeq;
import de.uka.ilkd.keyabs.rule.metaconstruct.MethodInvoc2MethodLabel;


/**
 * Abstract class factoring out commonalities of typcial term transformer implementations. 
 * The available singletons of term transformers are kept here.
 */
public abstract class AbstractTermTransformer extends AbstractSortedOperator 
                                           implements TermTransformer {

    private static final HashMap<String, AbstractTermTransformer> name2metaop 
    	= new HashMap<String, AbstractTermTransformer>(70);
    
    //must be first
    public static final Sort METASORT = new SortImpl(new Name("Meta"));    
    
    public static final AbstractTermTransformer META_ADD = new MetaAdd();

    public static final AbstractTermTransformer META_SUB = new MetaSub();

    public static final AbstractTermTransformer META_MUL = new MetaMul();

    public static final AbstractTermTransformer META_DIV = new MetaDiv();

    public static final AbstractTermTransformer META_LESS = new MetaLess();

    public static final AbstractTermTransformer META_GREATER = new MetaGreater();

    public static final AbstractTermTransformer META_LEQ = new MetaLeq();

    public static final AbstractTermTransformer META_GEQ = new MetaGeq();

    public static final AbstractTermTransformer META_EQ = new MetaEqual();

    public static final AbstractTermTransformer META_INT_AND = new MetaJavaIntAnd();

    public static final AbstractTermTransformer META_INT_OR = new MetaJavaIntOr();

    public static final AbstractTermTransformer META_INT_XOR = new MetaJavaIntXor();

    public static final AbstractTermTransformer META_INT_SHIFTRIGHT = new MetaJavaIntShiftRight();

    public static final AbstractTermTransformer META_INT_SHIFTLEFT = new MetaJavaIntShiftLeft();

    public static final AbstractTermTransformer META_INT_UNSIGNEDSHIFTRIGHT = new MetaJavaIntUnsignedShiftRight();

    public static final AbstractTermTransformer META_LONG_AND = new MetaJavaLongAnd();

    public static final AbstractTermTransformer META_LONG_OR = new MetaJavaLongOr();

    public static final AbstractTermTransformer META_LONG_XOR = new MetaJavaLongXor();

    public static final AbstractTermTransformer META_LONG_SHIFTRIGHT = new MetaJavaLongShiftRight();

    public static final AbstractTermTransformer META_LONG_SHIFTLEFT = new MetaJavaLongShiftLeft();

    public static final AbstractTermTransformer META_LONG_UNSIGNEDSHIFTRIGHT = new MetaJavaLongUnsignedShiftRight();

    public static final AbstractTermTransformer WHILE_INV_RULE = new WhileInvRule();
    
    public static final AbstractTermTransformer ENHANCEDFOR_INV_RULE = new EnhancedForInvRule();

    public static final AbstractTermTransformer ARRAY_BASE_INSTANCE_OF = new ArrayBaseInstanceOf();

    public static final AbstractTermTransformer CONSTANT_VALUE = new ConstantValue();
    
    public static final AbstractTermTransformer ENUM_CONSTANT_VALUE = new EnumConstantValue();
    
    public static final AbstractTermTransformer DIVIDE_MONOMIALS = new DivideMonomials ();

    public static final AbstractTermTransformer DIVIDE_LCR_MONOMIALS = new DivideLCRMonomials ();

    public static final AbstractTermTransformer INTRODUCE_ATPRE_DEFINITIONS = new IntroAtPreDefsOp();
    
    public static final AbstractTermTransformer MEMBER_PV_TO_FIELD = new MemberPVToField();

    public static final AbstractTermTransformer ADD_CAST = new AddCast();    

    public static final AbstractTermTransformer EXPAND_QUERIES = new ExpandQueriesMetaConstruct();
    
    public static final AbstractTermTransformer ABS_METHOD_ARGUMENTS_TO_SEQUENCE = new MethodArgsToSeq();
    
    public static final AbstractTermTransformer ABS_METHOD_INVOCATION_TO_METHOD_LABEL = 
	    new MethodInvoc2MethodLabel();

    public static final AbstractTermTransformer ABS_THIS_VARIABLE = 
	    new GetThisReference();

    
    protected static final TermFactory termFactory = TermFactory.DEFAULT;
    protected static final JavaDLTermBuilder TB = JavaProfile.DF();
    
    
    private static Sort[] createMetaSortArray(int arity) {
	Sort[] result = new Sort[arity];
	for(int i = 0; i < arity; i++) {
	    result[i] = METASORT;
	}
	return result;
    }
    
    
    protected AbstractTermTransformer(Name name, int arity, Sort sort) {
	super(name, createMetaSortArray(arity), sort, false);
	name2metaop.put(name.toString(), this);	
    }
    
    
   protected AbstractTermTransformer(Name name, int arity) {
	this(name, arity, METASORT);
    }


    
    public static TermTransformer name2metaop(String s) {
	return name2metaop.get(s);
    }


    /** @return String representing a logical integer literal 
     *  in decimal representation
     */
    public static String convertToDecimalString(Term term, IServices services) {
      	StringBuilder result = new StringBuilder();
	boolean neg = false;
	
	Operator top = term.op();
	IntegerLDT intModel = services.getTypeConverter().getIntegerLDT();	    
	final Operator numbers = intModel.getNumberSymbol();
	final Operator base    = intModel.getNumberTerminator();
	final Operator minus   = intModel.getNegativeNumberSign();
	// check whether term is really a "literal"
	
	if (top != numbers) {
	    Debug.out("abstractmetaoperator: Cannot convert to number:", term);
	    throw (new NumberFormatException());
	}
	
	term = term.sub(0);
	top = term.op();

	while (top == minus) {
	    neg=!neg;
	    term = term.sub(0);
	    top = term.op();
	}

	while (top != base) {
	    result.insert(0, top.name());
	    term = term.sub(0);
	    top = term.op();
	}
	
	if (neg) {
	    result.insert(0,"-");
	}
	
	return result.toString();
    }
            
    @Override    
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            IServices services) {
	// by default meta operators do not match anything 	
        return null;
    }    
}
