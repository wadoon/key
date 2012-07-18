package de.uka.ilkd.key.java;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

public abstract class AbstractTypeConverter {

    private final IServices services;

    public abstract AbstractTypeConverter copy(IServices services);

    public abstract boolean isBooleanType(Type t);

    public abstract boolean isNullType(Type t);

    public abstract boolean isReferenceType(Type t);

    public abstract boolean isIntegralType(Type t);

    public abstract boolean isArithmeticType(Type t);

    public abstract boolean isCastingTo(Type from, Type to);

    public abstract boolean isAssignableTo(Expression expr, Type to, ExecutionContext ec);

    public abstract boolean isAssignableTo(Type from, Type to);

    public abstract boolean isIdentical(Type from, Type to);

    public abstract boolean isIntegerType(Type t2);

    public abstract Term convertToLogicElement(ProgramElement pe, ExecutionContext ec);

    public abstract Term convertToLogicElement(ProgramElement pe);

    protected IntegerLDT integerLDT;
    protected BooleanLDT booleanLDT;
    protected LocSetLDT locSetLDT;
    protected HeapLDT heapLDT;
    protected SeqLDT seqLDT;
    @SuppressWarnings("unused")
    private FloatLDT floatLDT;
    @SuppressWarnings("unused")
    private DoubleLDT doubleLDT;
    protected CharListLDT charListLDT;
    protected ImmutableList<LDT> models = ImmutableSLList.<LDT>nil();

    protected AbstractTypeConverter(IServices services) {
        this.services = services;
    }

    /**
     * initializes the type converter with an LDT
     */
    public void init(LDT ldt) {	
        if (ldt instanceof IntegerLDT) {
            this.integerLDT = (IntegerLDT) ldt;
        } else if (ldt instanceof BooleanLDT) {
            this.booleanLDT = (BooleanLDT) ldt;
        } else if (ldt instanceof LocSetLDT) {
            this.locSetLDT = (LocSetLDT) ldt;
        } else if (ldt instanceof HeapLDT) {
            this.heapLDT = (HeapLDT) ldt;
        } else if (ldt instanceof SeqLDT) {
            this.seqLDT = (SeqLDT) ldt;
        } else if (ldt instanceof FloatLDT ) {
            this.floatLDT = (FloatLDT) ldt;
        } else if (ldt instanceof DoubleLDT) {
            this.doubleLDT = (DoubleLDT) ldt;
        } else if (ldt instanceof CharListLDT) {
            this.charListLDT = (CharListLDT) ldt;
        }
    
        this.models = this.models.prepend(ldt);
        Debug.out("Initialize LDTs: ", ldt);
    }

    public void init(ImmutableList<LDT> ldts) {
        for (LDT ldt : ldts) {
            init(ldt);
        }
    }

    public IServices getServices() {
        return services;
    }

    public ImmutableList<LDT> getModels() {
        return models;
    }

    public LDT getModelFor(Sort s) {
        for(LDT ldt : models) {
            if(s.equals(ldt.targetSort())) {
        	return ldt;
            }
        }
        Debug.out("No LDT found for ", s);
        return null;
    }

    public IntegerLDT getIntegerLDT() {
        return integerLDT;
    }

    public BooleanLDT getBooleanLDT() {
        return booleanLDT;
    }

    public LocSetLDT getLocSetLDT() {
        return locSetLDT;
    }

    public HeapLDT getHeapLDT() {
        return heapLDT;
    }

    public SeqLDT getSeqLDT() {
        return seqLDT;
    }

    public CharListLDT getCharListLDT() {
        return charListLDT;
    }

    public KeYJavaType getBooleanType() {
        return services.getJavaInfo()
                       .getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

    public Sort getPrimitiveSort(Type t) {
        return services.getJavaInfo().getKeYJavaType(t).getSort();
    }

    /** 
     * Retrieves the static type of the expression. This method may only be called
     * if the expressions type can be determined without knowledge of context 
     * information, i.e. it must not be a expression with an ex-/or implicit this 
     * reference like this.a or a methodcall whose value can only be determined
     * when one knows the exact invocation context. 
     * 
     * For these cases please use @link #getKeYJavaType(Expression, ExecutionContext)
     * 
     * This method behaves same as invoking <code>getKeYJavaType(e, null)</code>
     */
    public KeYJavaType getKeYJavaType(Expression e) {
        return getKeYJavaType(e, null);
    }

    /** 
     * retrieves the type of the expression <tt>e</tt> with respect to 
     * the context in which it is evaluated
     * @param e the Expression whose type has to be retrieved
     * @param ec the ExecutionContext of expression <tt>e</tt>
     * @return the KeYJavaType of expression <tt>e</tt>
     */
    public KeYJavaType getKeYJavaType(Expression e, ExecutionContext ec) {
        if(e instanceof ThisReference){
            return ec.getTypeReference().getKeYJavaType();
        }	
        return e.getKeYJavaType(services, ec);
    }

    /**
     * converts a logical term to an AST node if possible. If this fails
     * it throws a runtime exception.
     * @param term the Term to be converted
     * @return the Term as an program AST node of type expression
     * @throws RuntimeException iff a conversion is not possible
     */
    public Expression convertToProgramElement(Term term) {
        assert term != null;
        if (term.op() == heapLDT.getNull()) {
            return NullLiteral.NULL;
        } else if (term.op() instanceof Function) {
            for(LDT model : models) {
                if (model.hasLiteralFunction((Function)term.op())) {
                    return model.translateTerm(term, null);	       
                }
            }
        }
        
        final ExtList children = new ExtList();
        for (int i=0; i<term.arity(); i++) {
            children.add(convertToProgramElement(term.sub(i)));
        }
        if (term.op() instanceof ProgramInLogic) {
            return ((ProgramInLogic)term.op()).convertToProgram(term, children);
        } else if (term.op() instanceof Function) {
            for(LDT model : models) {
                if (model.containsFunction((Function)term.op())) {             
                    return model.translateTerm(term, children);
                }  
            }
        } 
        throw new RuntimeException("Cannot convert term to program: "+term
        			   +" "+term.op().getClass());
    }

    public KeYJavaType getKeYJavaType(Term t) {
        KeYJavaType result = null;
        final IProgramInfo info = services.getProgramInfo();
        if (info.isReferenceSort(t.sort())) {
            result = info.getKeYJavaType(t.sort());
        } else if(t.op() instanceof Function) {
            for(LDT ldt : models) {
        	if(ldt.containsFunction((Function)t.op())) {
        	    Type type = ldt.getType(t);
        	    result = info.getKeYJavaType(type);
        	    break;
        	}
            }
        }
        
        if(result == null) {
            //HACK
            result = info.getKeYJavaType(t.sort().toString()); 
        }
        if (result == null) {
           result = getKeYJavaType(convertToProgramElement(t));
        }
    
        return result;
    }

    public KeYJavaType getKeYJavaType(Type t) { 
        return services.getJavaInfo().getKeYJavaType(t);
    }

    public abstract KeYJavaType getPromotedType(KeYJavaType keYJavaType);

    public KeYJavaType getPromotedType(KeYJavaType keYJavaType,
            KeYJavaType keYJavaType2) {
        // TODO Auto-generated method stub
        return null;
    }

    public boolean isImplicitNarrowing(Expression expressionAt,
            PrimitiveType javaType) {
        // TODO Auto-generated method stub
        return false;
    }

}