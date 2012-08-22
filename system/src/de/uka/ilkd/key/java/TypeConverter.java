// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;


import recoder.service.ConstantEvaluator;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.JavaDLTermBuilder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.Debug;


public final class TypeConverter extends AbstractTypeConverter {
    
    private static final JavaDLTermBuilder TB = JavaProfile.DF();

    public TypeConverter(Services s){
        super(s);
    }

    @Override
    public Services getServices() {
        return (Services) super.getServices();
    }
    
    private Term translateOperator
	(de.uka.ilkd.key.java.expression.Operator op, ExecutionContext ec) {

	final Term[] subs  = new Term[op.getArity()];
	for(int i = 0, n = op.getArity(); i < n; i++) {
	    subs[i] = convertToLogicElement(op.getExpressionAt(i), ec);
	}
	
	//hack: convert object singleton to location singleton
	if(op instanceof Singleton) {
	    assert heapLDT.getSortOfSelect(subs[0].op()) != null 
	           : "unexpected argument of \\singleton: " + subs[0];
	    return TB.singleton(getServices(), subs[0].sub(1), subs[0].sub(2));
	}	
	
	LDT responsibleLDT = null;
	if (integerLDT.isResponsible(op, subs, getServices(), ec)) {
	    responsibleLDT = integerLDT;
	} else if (booleanLDT.isResponsible(op, subs, getServices(), ec)) {
	    responsibleLDT = booleanLDT;
	} else if (locSetLDT.isResponsible(op, subs, getServices(), ec)) {
	    responsibleLDT = locSetLDT;
	} else if(seqLDT.isResponsible(op, subs, getServices(), ec)) {
	    responsibleLDT = seqLDT;
	} else if(charListLDT.isResponsible(op, subs, getServices(), ec)) {
	    responsibleLDT = charListLDT;
    	} else if(op instanceof Equals) {
	    assert subs.length == 2;
	    return TB.equals(subs[0], subs[1]);
	} else if(op instanceof Conditional) {
	    assert subs.length == 3;
	    return TB.ife(subs[0], subs[1], subs[2]);
	} else if(op instanceof DLEmbeddedExpression) {
	    DLEmbeddedExpression emb = (DLEmbeddedExpression) op;
	    Function f = emb.getFunctionSymbol();
	    // TODO make a sensible error recovery
	    return TB.func(f, subs);
	} else {
	    Debug.out("typeconverter: no data type model "+
		      "available to convert:", op, op.getClass());		
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this operator: " + op);
	}
	return TB.func(responsibleLDT.getFunctionFor(op, getServices(), ec), subs);
    }
   

    private Term convertReferencePrefix(ReferencePrefix prefix, 
					ExecutionContext ec) {
	Debug.out("typeconverter: (prefix, class)", prefix, 
		  (prefix != null ? prefix.getClass() : null));		
	if (prefix instanceof FieldReference) {
	    return convertVariableReference((FieldReference) prefix, ec);
	} else if (prefix instanceof MetaClassReference) {
	    Debug.out("typeconverter: "+
		      "WARNING: metaclass-references not supported yet");
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this");
	} else 	if (prefix instanceof ProgramVariable) {
	    // the base case: the leftmost item is a local variable
	    return TB.var((ProgramVariable)prefix);
	} else 	if (prefix instanceof VariableReference) {
	    Debug.out("typeconverter: "+
		      "variablereference:", (((VariableReference)prefix).getProgramVariable()));
	    return TB.var(((VariableReference)prefix).getProgramVariable());
	}  else if (prefix instanceof ArrayReference) {	   
	    return convertArrayReference((ArrayReference)prefix, ec);
	} else if (prefix instanceof ThisReference) {	 
	    if(prefix.getReferencePrefix()!=null && (prefix.getReferencePrefix() instanceof TypeReference)){
	        TypeReference tr = (TypeReference) prefix.getReferencePrefix();
	        KeYJavaType kjt = tr.getKeYJavaType();
	        return findThisForSortExact(kjt.getSort(), ec);
	    }
	    return convertToLogicElement(ec.getRuntimeInstance());
	} else {            
	    Debug.out("typeconverter: WARNING: unknown reference prefix:", 
		      prefix, prefix == null ? null : prefix.getClass());
	    throw new IllegalArgumentException("TypeConverter failed to convert "
					       + prefix);
	}
    }
    
    
    public Term findThisForSortExact(Sort s, ExecutionContext ec){
        ProgramElement pe = ec.getRuntimeInstance();
        if(pe == null) return null;
        Term inst = convertToLogicElement(pe, ec);
        return findThisForSort(s, inst, ec.getTypeReference().getKeYJavaType(), true);
    
    }
    
    public Term findThisForSort(Sort s, ExecutionContext ec){
        ProgramElement pe = ec.getRuntimeInstance();
        if(pe == null) return null;
        Term inst = convertToLogicElement(pe, ec);
        return findThisForSort(s, inst, ec.getTypeReference().getKeYJavaType(), false);
    }
    
    
    public Term findThisForSort(Sort s, 
	    			Term self, 
	    			KeYJavaType context, 
	    			boolean exact) {
        Term result = self;
        LocationVariable inst;
        while(!exact && !context.getSort().extendsTrans(s) 
              || exact && !context.getSort().equals(s)){
            inst = (LocationVariable)
                    getServices().getJavaInfo().getAttribute(
                       ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, context);
            final Function fieldSymbol
            	= heapLDT.getFieldSymbolForPV(inst, getServices());
            result = TB.dot(getServices(), inst.sort(), result, fieldSymbol);
            context = inst.getKeYJavaType();
        }
        return result;      
    }

    
    public Term convertVariableReference(VariableReference fr,
					 ExecutionContext ec) {	       
	Debug.out("TypeConverter: FieldReference: ", fr);
	final ReferencePrefix prefix = fr.getReferencePrefix();
	final ProgramVariable var = fr.getProgramVariable();
	if(var instanceof ProgramConstant) {
	    return TB.var(var);
	} else if(var == getServices().getJavaInfo().getArrayLength()) {
	    return TB.dotLength(getServices(), convertReferencePrefix(prefix, ec));
	} else if(var.isStatic()) {
	    final Function fieldSymbol 
	    	= heapLDT.getFieldSymbolForPV((LocationVariable)var, getServices());
	    return TB.staticDot(getServices(), var.sort(), fieldSymbol);
	} else if(prefix == null) {
	    if(var.isMember()) {
		final Function fieldSymbol 
			= heapLDT.getFieldSymbolForPV((LocationVariable)var, 
						      getServices());
		return TB.dot(getServices(), 
			      var.sort(), 
			      findThisForSort(var.getContainerType().getSort(), 
				              ec), 
			      fieldSymbol);
	    } else {
		return TB.var(var);
	    }
	} else if (!(prefix instanceof PackageReference) ) {
	    final Function fieldSymbol 
	    	= heapLDT.getFieldSymbolForPV((LocationVariable)var, getServices());
	    return TB.dot(getServices(), var.sort(), convertReferencePrefix(prefix, ec), fieldSymbol);
	} 
	Debug.out("typeconverter: Not supported reference type (fr, class):",
		  fr, fr.getClass());
	throw new IllegalArgumentException
	    ("TypeConverter could not handle this");	
    }
    

    public Term convertArrayReference(ArrayReference ar, 
				      ExecutionContext ec){
        final Term[] index = new Term[ar.getDimensionExpressions().size()];
        final Term t = convertToLogicElement(ar.getReferencePrefix(), ec);
        for (int i=0; i<index.length; i++) { 
            index[i] = 
                convertToLogicElement(ar.getDimensionExpressions().get(i), ec);
        }
        assert index.length == 1 : "multi-dimensional arrays not implemented";
        return TB.dotArr(getServices(), t, index[0]);
    }

    private Term convertToInstanceofTerm(Instanceof io, 
					 ExecutionContext ec) {
	final KeYJavaType type = ((TypeReference)io.getChildAt(1)).
	    getKeYJavaType();
	final Term obj = convertToLogicElement(io.getChildAt(0), ec);
	final Sort s = type.getSort();
	final Function instanceOfSymbol = s.getInstanceofSymbol(getServices()); 
	
	// in JavaDL S::instance(o) is also true if o (for reference types S)
	// is null in opposite to Java
	// we create here if (obj = null) then FALSE else S::instance(obj) 				      
	return TB.ife(TB.equals(obj, TB.NULL(getServices())), TB.FALSE(getServices()), 
                TB.func(instanceOfSymbol, obj));
    }
  

    @Override
    public Term convertToLogicElement(ProgramElement pe) {
	return convertToLogicElement(pe, null);	
    }

    
    @Override
    public Term convertToLogicElement(ProgramElement pe, 				    
				      ExecutionContext ec) {
	Debug.out("typeconverter: called for:", pe, pe.getClass());
	if (pe instanceof ProgramVariable) {	  
	    return TB.var((ProgramVariable)pe);
	} else if (pe instanceof FieldReference) {
	    return convertVariableReference((FieldReference)pe, ec);
	} else if (pe instanceof VariableReference) {
	    return convertVariableReference((VariableReference)pe, ec);
	} else if (pe instanceof ArrayReference){
	    return convertArrayReference((ArrayReference)pe, ec);
	} else if (pe instanceof Literal) {
	    return convertLiteralExpression((Literal)pe);
	} else if (pe instanceof Negative
	        && ((Negative)pe).getChildAt(0) instanceof IntLiteral) {
	    String val = ((IntLiteral)((Negative)pe).getChildAt(0)).getValue();
	    if (val.charAt(0)=='-') {
		return integerLDT.translateLiteral
		    (new IntLiteral(val.substring(1)), getServices());
	    } else {
		return integerLDT.translateLiteral
		    (new IntLiteral("-"+val), getServices());
	    }
	} else if (pe instanceof Negative 
		   && ((Negative)pe).getChildAt(0) instanceof LongLiteral ) {
	    String val = ((LongLiteral)
			  ((Negative)pe).getChildAt(0)).getValue();
	    if (val.charAt(0)=='-') {
		return integerLDT.translateLiteral
		    (new LongLiteral(val.substring(1)), getServices());
	    } else {
		return integerLDT.translateLiteral
		    (new LongLiteral("-"+val), getServices());
	    }
	} else if (pe instanceof ThisReference) {
	    return convertReferencePrefix((ThisReference)pe, ec);
	} else if (pe instanceof ParenthesizedExpression) {
            return convertToLogicElement
                (((ParenthesizedExpression)pe).getChildAt(0), ec);
        } else if (pe instanceof Instanceof) {
	    return convertToInstanceofTerm((Instanceof)pe, ec);
	} else if (pe instanceof de.uka.ilkd.key.java.expression.Operator) {
	    return translateOperator
		((de.uka.ilkd.key.java.expression.Operator)pe, ec);
	} else if (pe instanceof PrimitiveType) {
	    throw new IllegalArgumentException("TypeConverter could not handle"
					       +" this primitive type");
	} else if (pe instanceof MetaClassReference) {
	    assert false : "not supported";
        }  
	throw new IllegalArgumentException
	    ("TypeConverter: Unknown or not convertable ProgramElement " + pe+
             " of type "+pe.getClass());
    }

    
    /**
     * dispatches the given literal and converts it
     * @param lit the Literal to be converted
     * @return the Term representing <tt>lit</tt> in the logic
     */
    private Term convertLiteralExpression(Literal lit) {      
        if (lit instanceof BooleanLiteral) {   
            return booleanLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof NullLiteral) {
            return TB.NULL(getServices());
        } else if (lit instanceof IntLiteral) {
            return integerLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof CharLiteral) {
            return integerLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof LongLiteral) {
            return integerLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof StringLiteral) {
            return charListLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof EmptySetLiteral) {
            return locSetLDT.translateLiteral(lit, getServices());
        } else if (lit instanceof EmptySeqLiteral) {
            return seqLDT.translateLiteral(lit, getServices());            
        } else {
            Debug.fail("Unknown literal type", lit);                 
            return null;
        }
    }
    

    public static boolean isArithmeticOperator
	(de.uka.ilkd.key.java.expression.Operator op) {
	if (op instanceof Divide || op instanceof Times || 
	    op instanceof Plus || op instanceof Minus || 
	    op instanceof Modulo || op instanceof ShiftLeft ||
	    op instanceof ShiftRight || op instanceof BinaryAnd || 
	    op instanceof BinaryNot || op instanceof BinaryOr || 
	    op instanceof BinaryXOr || op instanceof Negative || 
	    op instanceof PreIncrement || op instanceof PostIncrement ||
	    op instanceof PreDecrement || op instanceof PostDecrement) {
	    return true;
	} 
	return false;
    }

    
    /**
     * performs binary numeric promotion on the argument types
     */
    public KeYJavaType getPromotedType(KeYJavaType type1, 
            			       KeYJavaType type2) {
        final Type t1 = type1.getJavaType();
        final Type t2 = type2.getJavaType();

        if ((t1 == PrimitiveType.JAVA_BOOLEAN &&
                t2 == PrimitiveType.JAVA_BOOLEAN)) {
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        } else if ((t1 == PrimitiveType.JAVA_BYTE ||
                t1 == PrimitiveType.JAVA_SHORT ||
                t1 == PrimitiveType.JAVA_CHAR||
                t1 == PrimitiveType.JAVA_INT) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_INT)) {
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    	} else if ((t2 == PrimitiveType.JAVA_LONG) &&
                (t1 == PrimitiveType.JAVA_BYTE||
                        t1 == PrimitiveType.JAVA_SHORT||
                        t1 == PrimitiveType.JAVA_INT||
                        t1 == PrimitiveType.JAVA_CHAR||
                        t1 == PrimitiveType.JAVA_LONG)) { 
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
    	} else if ((t1 == PrimitiveType.JAVA_LONG) &&
                (t2 == PrimitiveType.JAVA_BYTE||
                        t2 == PrimitiveType.JAVA_SHORT||
                        t2 == PrimitiveType.JAVA_INT||
                        t2 == PrimitiveType.JAVA_CHAR||
                        t2 == PrimitiveType.JAVA_LONG)) { 
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
    	} else if ((t1 == PrimitiveType.JAVA_BIGINT) && isIntegerType(t2)) {
    	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        } else if ((t2 == PrimitiveType.JAVA_BIGINT) && isIntegerType(t2)) {
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
    	} else if (t1 == PrimitiveType.JAVA_LOCSET && t2 == PrimitiveType.JAVA_LOCSET) { 
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LOCSET);
    	} else if (t1 == PrimitiveType.JAVA_SEQ && t2 == PrimitiveType.JAVA_SEQ) { 
            return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    	} else if (type1.equals(getServices().getJavaInfo().getKeYJavaType("java.lang.String"))) { 
            return type1;
    	} else if (type2.equals(getServices().getJavaInfo().getKeYJavaType("java.lang.String"))) { 
            return type2;
        } else {
            throw new RuntimeException("Could not determine promoted type "
        	    	               + "of " + t1 + " and " + t2);
        }
    }

    @Override
    public boolean isIntegerType(Type t2){
        return (t2 == PrimitiveType.JAVA_BYTE || t2 == PrimitiveType.JAVA_CHAR || t2 == PrimitiveType.JAVA_INT
                || t2 == PrimitiveType.JAVA_LONG || t2 == PrimitiveType.JAVA_SHORT || t2 == PrimitiveType.JAVA_BIGINT);
    }


    // this method performs unary numeric promotion on the arguments
    public KeYJavaType getPromotedType(KeYJavaType type1) {
        final Type t1 = type1.getJavaType();
	if (t1 == PrimitiveType.JAVA_BOOLEAN)
	    // not really numeric ...
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
	if (t1 == PrimitiveType.JAVA_BYTE ||
	    t1 == PrimitiveType.JAVA_SHORT||
	    t1 == PrimitiveType.JAVA_CHAR||
	    t1 == PrimitiveType.JAVA_INT)
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
	if (t1 == PrimitiveType.JAVA_LONG)
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
	if (t1 == PrimitiveType.JAVA_LOCSET) 
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LOCSET);
	if (t1 == PrimitiveType.JAVA_SEQ) 
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);	
	if (t1 == PrimitiveType.JAVA_BIGINT)
	    return getServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
	throw new RuntimeException("Could not determine promoted type "+
				   "of "+type1);
    }


    /** These methods are taken from recoder (and modified) */
    public boolean isWidening(PrimitiveType from, PrimitiveType to) {
	// we do not handle null's
	if (from == null || to == null) return false;
	// equal types can be coerced
	if (from == to ) return true;
	// boolean types cannot be coerced into something else
	if (from == PrimitiveType.JAVA_BOOLEAN ||
	    to == PrimitiveType.JAVA_BOOLEAN)	    
	    return false;
	// everything else can be coerced to a double
	if (to == PrimitiveType.JAVA_DOUBLE) return true;
	// but a double cannot be coerced to anything else
	if (from == PrimitiveType.JAVA_DOUBLE) return false;
	// everything except doubles can be coerced to a float
	if (to == PrimitiveType.JAVA_FLOAT) return true;
	// but a float cannot be coerced to anything but float or double
	if (from == PrimitiveType.JAVA_FLOAT) return false;	
	// everything except float or double can be coerced to a long
	if (to == PrimitiveType.JAVA_LONG) return true;
	// but a long cannot be coerced to anything but float, double or long
	if (from == PrimitiveType.JAVA_LONG) return false;
	// everything except long, float or double can be coerced to an int
	if (to == PrimitiveType.JAVA_INT) return true;
	// but an int cannot be coerced to the remaining byte, char, short
	if (from == PrimitiveType.JAVA_INT) return false;
	// between byte, char, short, only one conversion is admissible
	return (from == PrimitiveType.JAVA_BYTE &&
		to == PrimitiveType.JAVA_SHORT);
    }

    
    public boolean isWidening(ClassType from, ClassType to) {
	return isWidening ( getKeYJavaType ( from ),
			    getKeYJavaType ( to   ) );
    }
    

    public boolean isWidening(ArrayType from, ArrayType to) {
	KeYJavaType toBase   =  to.getBaseType().getKeYJavaType();
	if (toBase == 
	    getServices().getJavaInfo().getJavaLangObject() ) { // seems incorrect
	    return true;
	}
	KeYJavaType fromBase = from.getBaseType().getKeYJavaType();
	if (toBase.getJavaType () instanceof PrimitiveType) {
	    return toBase == fromBase;
	}
	return isWidening(fromBase, toBase);
    }
    
    
    public boolean isWidening(Type from, Type to) {
	if ( from instanceof KeYJavaType )
	    return isWidening ( (KeYJavaType)from,
				getKeYJavaType ( to ) );
	if ( to   instanceof KeYJavaType )
	    return isWidening ( getKeYJavaType ( from ),
				(KeYJavaType)to );

	if (from instanceof ClassType) {
	    return isWidening ( getKeYJavaType ( from ),
				getKeYJavaType ( to   ) );
	} else if (from instanceof PrimitiveType) {
	    if (to instanceof PrimitiveType) {
		return isWidening((PrimitiveType)from, (PrimitiveType)to);
	    }
	} else if (from instanceof ArrayType) {
	    if (to instanceof ClassType) {
                final Sort toSort = getKeYJavaType ( to ).getSort(); 		
		return getServices().getJavaInfo().isAJavaCommonSort(toSort);
	    } else if (to instanceof ArrayType) {
		return isWidening((ArrayType)from, (ArrayType)to);
	    }
	}
	return false;
    }    

    
    // this also handles class types
    public boolean isWidening(KeYJavaType from, KeYJavaType to) {
	Type a = from.getJavaType ();
	Type b = to  .getJavaType ();

	if ( a instanceof ClassType || a == null ) {
	    return
		from.getSort ().extendsTrans ( to.getSort () ) ||
		( a == NullType.JAVA_NULL &&
		  b instanceof ArrayType );
	} else {
	    if ( b == null )
		return
		    to == getServices().getJavaInfo().
		    getJavaLangObject () &&
		    a instanceof ArrayType;
	    else
		return isWidening ( a, b );
	}
    }


    public boolean isImplicitNarrowing
	(Expression expr, PrimitiveType to) {
	
	int minValue, maxValue;
	if (to == PrimitiveType.JAVA_BYTE) {
	    minValue = Byte.MIN_VALUE;
	    maxValue = Byte.MAX_VALUE;
	} else if (to == PrimitiveType.JAVA_CHAR) {
	    minValue = Character.MIN_VALUE;
	    maxValue = Character.MAX_VALUE;
	} else if (to == PrimitiveType.JAVA_SHORT) {
	    minValue = Short.MIN_VALUE;
	    maxValue = Short.MAX_VALUE;
	} else {
	    return false;
	}

	ConstantExpressionEvaluator cee = 
	    getServices().getConstantExpressionEvaluator();

	ConstantEvaluator.EvaluationResult res = 
	    new ConstantEvaluator.EvaluationResult();

	if (!cee.isCompileTimeConstant(expr, res) || 
	    res.getTypeCode() != ConstantEvaluator.INT_TYPE) {
	    return false;
	}
	int value = res.getInt();
	return (minValue <= value) && (value <= maxValue);	
    }

    
    @Override
    public boolean isIdentical ( Type from, Type to ) {
    	// XXX causes bug #1163
//		from = getKeYJavaType ( from );
//		to   = getKeYJavaType ( to   );
    	return from == to;
    }

    
    @Override
    public boolean isAssignableTo ( Type from, Type to ) {
	return isIdentical ( from, to ) || isWidening ( from, to );
    }

    
    @Override
    public boolean isAssignableTo ( Expression expr, Type to, ExecutionContext ec ) {
	return
	    ( to instanceof PrimitiveType &&
	      isImplicitNarrowing ( expr, (PrimitiveType)to ) ) ||
	    isIdentical ( expr.getKeYJavaType ( getServices(), ec ), to ) ||
	    isWidening  ( expr.getKeYJavaType ( getServices(), ec ), to );
    }

    
    // this also handles class types
    public boolean isNarrowing(KeYJavaType from, KeYJavaType to) {
	Type a = from.getJavaType ();
	Type b = to  .getJavaType ();

	if ( a instanceof ClassType || a == null ) {
	    return
		to.getSort ().extendsTrans ( from.getSort () ) ||
		( from == getServices().
		  getJavaInfo().getJavaLangObject () &&
		  a instanceof ArrayType );
	} else {
	    if ( b == null )
		return false;
	    else
		return isNarrowing ( a, b );
	}
    }

    
    public boolean isNarrowing(PrimitiveType from, PrimitiveType to) {
	// we do not handle null's
	if (from == null || to == null) return false;

	if (from == PrimitiveType.JAVA_BYTE) {
	    return (to == PrimitiveType.JAVA_CHAR );
	}
	if (from == PrimitiveType.JAVA_SHORT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_CHAR);
	}
	if (from == PrimitiveType.JAVA_CHAR) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT);
	}
	if (from == PrimitiveType.JAVA_INT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR);
	}
	if (from == PrimitiveType.JAVA_LONG) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT);
	}
	if (from == PrimitiveType.JAVA_FLOAT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT ||
		    to == PrimitiveType.JAVA_LONG);
	}
	if (from == PrimitiveType.JAVA_DOUBLE) {
	    return (to == PrimitiveType.JAVA_BYTE ||
		    to == PrimitiveType.JAVA_SHORT ||
		    to == PrimitiveType.JAVA_CHAR ||
		    to == PrimitiveType.JAVA_INT ||
		    to == PrimitiveType.JAVA_LONG ||
		    to == PrimitiveType.JAVA_FLOAT);
	}
	if (from == PrimitiveType.JAVA_BIGINT) {
	    return (to == PrimitiveType.JAVA_BYTE ||
			    to == PrimitiveType.JAVA_SHORT ||
			    to == PrimitiveType.JAVA_CHAR ||
			    to == PrimitiveType.JAVA_INT ||
			    to == PrimitiveType.JAVA_LONG ||
			    to == PrimitiveType.JAVA_FLOAT ||
			    to == PrimitiveType.JAVA_DOUBLE);
		}
	return false;
    }
    

    public boolean isNarrowing(ClassType from, ClassType to) {
	return isNarrowing ( getKeYJavaType ( from ),
			     getKeYJavaType ( to   ) );
    }
    

    public boolean isNarrowing(ArrayType from, ArrayType to) {
	KeYJavaType toBase   = to.getBaseType().getKeYJavaType();
	KeYJavaType fromBase = from.getBaseType().getKeYJavaType();
	return
	    isReferenceType ( toBase   ) &&
	    isReferenceType ( fromBase ) &&
	    isNarrowing(fromBase, toBase);
    }
    

    public boolean isNarrowing(Type from, Type to) {
	if ( from instanceof KeYJavaType )
	    return isNarrowing ( (KeYJavaType)from,
				getKeYJavaType ( to ) );
	if ( to   instanceof KeYJavaType )
	    return isNarrowing ( getKeYJavaType ( from ),
				(KeYJavaType)to );

	if (from instanceof ClassType) {
	    return isNarrowing ( getKeYJavaType ( from ),
				 getKeYJavaType ( to   ) );
	} else if (from instanceof PrimitiveType) {
	    if (to instanceof PrimitiveType) {
		return isNarrowing((PrimitiveType)from, (PrimitiveType)to);
	    }
	} else if (from instanceof ArrayType) {
	    if (to instanceof ArrayType) {
		return isNarrowing((ArrayType)from, (ArrayType)to);
	    }
	}
	return false;
    }

    
    @Override
    public boolean isCastingTo ( Type from, Type to ) {
	// there is currently no interface handling

	// identity conversion
	if ( isIdentical ( from, to ) )
	    return true;

	// conversions between numeric types are always possible
	if ( isArithmeticType ( from ) &&
	     isArithmeticType ( to   ) )
	    return true;

	// all widening conversions
	if ( isWidening ( from, to ) )
	    return true;

	// narrowing
	return isNarrowing ( from, to );
    }

    
    @Override
    public boolean isArithmeticType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG   ||
	    t == PrimitiveType.JAVA_BIGINT ||
	    t == PrimitiveType.JAVA_FLOAT  ||
	    t == PrimitiveType.JAVA_DOUBLE;
    }

    
    @Override
    public boolean isIntegralType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BYTE   ||
	    t == PrimitiveType.JAVA_SHORT  ||
	    t == PrimitiveType.JAVA_INT    ||
	    t == PrimitiveType.JAVA_CHAR   ||
	    t == PrimitiveType.JAVA_LONG   ||
	    t == PrimitiveType.JAVA_BIGINT;
    }

    
    @Override
    public boolean isReferenceType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    // there is currently no interface handling
	    t == null ||
	    ( t instanceof ClassType && !( t instanceof NullType ) ) ||
	    t instanceof ArrayType;
    }
    

    @Override
    public boolean isNullType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == NullType.JAVA_NULL;
    }
    

    @Override
    public boolean isBooleanType ( Type t ) {
	if ( t instanceof KeYJavaType )
	    t = ((KeYJavaType)t).getJavaType ();
	return
	    t == PrimitiveType.JAVA_BOOLEAN;
    }
    

    @Override
    public TypeConverter copy(IServices services) {
	final TypeConverter tc = new TypeConverter((Services) services);
	tc.init(models);
	return tc;
    }

    @Override
    public KeYJavaType getBooleanType() {
        return services.getJavaInfo()
                       .getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }
}
