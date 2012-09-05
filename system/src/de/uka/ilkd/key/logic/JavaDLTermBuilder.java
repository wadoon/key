package de.uka.ilkd.key.logic;

import java.io.StringReader;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.IProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.OpReplacer;

public class JavaDLTermBuilder extends TermBuilder<Services> {

    public static JavaDLTermBuilder DF = new JavaDLTermBuilder();
    
    private JavaDLTermBuilder() {
    }

    @Override
    public Term parseTerm(String s, IServices services) throws ParserException {
        return parseTerm(s, services, services.getNamespaces());
    }

    /**
     * Parses the given string that represents the term (or createTerm) using the
     * provided namespaces.
     * 
     * @param s
     *            the String to parse
     * @param services
     *            the services to be used for parsing
     * @param namespaces
     *            the namespaces used for name lookup.
     */
    @Override
    public Term parseTerm(String s, IServices services, NamespaceSet namespaces)
            throws ParserException {
        AbbrevMap abbr = (services.getProof() == null)
                ? null : services.getProof().abbreviations();
        Term term = new DefaultTermParser().parse(
                new StringReader(s), null, services, namespaces, abbr);
        return term;
    }

    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(IServices services, KeYJavaType kjt, boolean makeNameUnique) {
        String name = "self";
        if(makeNameUnique) {
            name = newName(services, name);
        }
        return new LocationVariable(new ProgramElementName(name), kjt);
    }

    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
    public LocationVariable selfVar(IServices services, IProgramMethod pm, KeYJavaType kjt, boolean makeNameUnique) {
        if(pm.isStatic()) {
            return null;
        } else {
            return selfVar(services, kjt, makeNameUnique);
        }
    }

    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
    public ImmutableList<ProgramVariable> paramVars(IServices services, IObserverFunction obs, boolean makeNamesUnique) {
        ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil(); 
        for(int i = 0, n = obs.getNumParams(); i < n; i++) {
            final KeYJavaType paramType = obs.getParamType(i);
            String name; 
            if(obs instanceof IProgramMethod) {
        	name = ((IProgramMethod)obs).getParameterDeclarationAt(i)
        	                           .getVariableSpecification()
        	                           .getName();
            } else {
        	name = paramType.getSort().name().toString().charAt(0) + "";
            }
            if(makeNamesUnique) {
        	name = newName(services, name);
            }
            final LocationVariable paramVar
            	= new LocationVariable(new ProgramElementName(name), paramType);
            result = result.append(paramVar);
        }        
        return result;
    }

    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
    public ImmutableList<ProgramVariable> paramVars(IServices services, String postfix, IObserverFunction obs, boolean makeNamesUnique) {
        final ImmutableList<ProgramVariable> paramVars 
        	= paramVars(services, obs, true);
        ImmutableList<ProgramVariable> result 
        	= ImmutableSLList.<ProgramVariable>nil();
        for(ProgramVariable paramVar : paramVars) {
            ProgramElementName pen 
                = new ProgramElementName(paramVar.name() + postfix);            
            LocationVariable formalParamVar
            	= new LocationVariable(pen, paramVar.getKeYJavaType());
            result = result.append(formalParamVar);
        }
        return result;
    }

    /**
     * Creates a program variable for the result. Take care to register it
     * in the namespaces.
     */
    public LocationVariable resultVar(IServices services, IProgramMethod pm, boolean makeNameUnique) {
        return resultVar(services, "result", pm, makeNameUnique);
    }

    /**
     * Creates a program variable for the result with passed name. Take care to
     * register it in the namespaces.
     */
    public LocationVariable resultVar(IServices services, String name, IProgramMethod pm, boolean makeNameUnique) {
        if(pm.isVoid() || pm.isConstructor()) {
            return null;
        } else {
            if(makeNameUnique) {
        	name = newName(services, name);
            }
            return new LocationVariable(new ProgramElementName(name),
        			    	pm.getReturnType());
        }
    }

    /**
     * Creates a program variable for the thrown exception. Take care to 
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services, IProgramMethod pm, boolean makeNameUnique) {
        return excVar(services, "exc", pm, makeNameUnique);
    }

    /**
     * Creates a program variable for the thrown exception. Take care to 
     * register it in the namespaces.
     */
    public LocationVariable excVar(Services services, String name, IProgramMethod pm, boolean makeNameUnique) {
        if(makeNameUnique) {
            name = newName(services, name);
        }	
        return new LocationVariable(new ProgramElementName(name),
                                    services.getJavaInfo().getTypeByClassName(
                                                   "java.lang.Exception"));
    }

    public Term inInt(Term var, Services services) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inInt"));
        return func(f, var);
    }

    public Term staticDot(Services services, Sort asSort, Term f) {
        return dot(services, asSort, NULL(services), f);
    }

    public Term staticDot(Services services, Sort asSort, Function f) {
        final Sort fieldSort 
        	= services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? staticDot(services, asSort, func(f))
               : func(f, getBaseHeap(services));
    }

    public Term arr(Services services, Term idx) {
        return func(services.getTypeConverter().getHeapLDT().getArr(), idx);
    }

    public Term dotArr(Services services, Term ref, Term idx) {
        if(ref == null || idx == null) {
            throw new TermCreationException("Tried to build an array access "+
                    "term without providing an " +
                    (ref==null ? "array reference." : "index.") + 
                    "("+ref+"["+idx+"])");
        }   
                
        final Sort elementSort;
        if(ref.sort() instanceof ArraySort) {
            elementSort = ((ArraySort) ref.sort()).elementSort();
        } else {
            throw new TermCreationException("Tried to build an array access "+
                    "on an inacceptable sort: " + ref.sort().getClass() + "\n" +
                    "("+ref+"["+idx+"])");
        }
        
        return select(services, 
        	      elementSort, 
        	      getBaseHeap(services), 
        	      ref, 
        	      arr(services, idx));
    }

    public Term dotLength(Services services, Term a) {
        final TypeConverter tc = services.getTypeConverter();
        return func(tc.getHeapLDT().getLength(), a); 
    }

    public Term created(Services services, Term h, Term o) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(select(services,
        	              tc.getBooleanLDT().targetSort(),
        		      h,
        	              o,
        	              func(tc.getHeapLDT().getCreated())),
        	       TRUE(services));
    }

    public Term created(Services services, Term o) {
        return created(services, getBaseHeap(services), o);
    }

    public Term initialized(Services services, Term o) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(dot(services,
        	          tc.getBooleanLDT().targetSort(),
        	          o,
        	          tc.getHeapLDT().getInitialized()),
        	      TRUE(services));
    }

    public Term classPrepared(Services services, Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(staticDot(services,
        	                tc.getBooleanLDT().targetSort(),
        	                tc.getHeapLDT().getClassPrepared(classSort, 
        	                				 services)),
        	      TRUE(services));	
    }

    public Term classInitialized(Services services, Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(staticDot(services,
        	                tc.getBooleanLDT().targetSort(),
        	                tc.getHeapLDT().getClassInitialized(classSort, 
        	        				            services)),
        	      TRUE(services));
    }

    public Term classInitializationInProgress(Services services, Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(staticDot(services,
        	                tc.getBooleanLDT().targetSort(),
        	                tc.getHeapLDT()
        	                  .getClassInitializationInProgress(classSort, 
        	        	   			            services)),
        	      TRUE(services));
    }

    public Term classErroneous(Services services, Sort classSort) {
        final TypeConverter tc = services.getTypeConverter();	
        return equals(staticDot(services,
        	                tc.getBooleanLDT().targetSort(),
        	                tc.getHeapLDT().getClassErroneous(classSort, 
        	        	 			          services)),
        	      TRUE(services));
    }

    public Term create(Services services, Term h, Term o) {
        return func(services.getTypeConverter().getHeapLDT().getCreate(), 
        	     new Term[]{h, o});
    }


    public Term reachableValue(Services services, Term h, Term t,
            KeYJavaType kjt) {
                assert t.sort().extendsTrans(kjt.getSort()) 
                       || t.sort() instanceof IProgramSVSort;
                final Sort s = t.sort() instanceof IProgramSVSort ? kjt.getSort() : t.sort();
                final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
                final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
                if(s.extendsTrans(services.getJavaInfo().objectSort())) {
                    return or(created(services, h, t), equals(t, NULL(services)));
                } else if(s.equals(setLDT.targetSort())) {
                    return createdInHeap(services, t, h);
                } else if(s.equals(intLDT.targetSort()) && kjt.getJavaType() != PrimitiveType.JAVA_BIGINT) {
                    return func(intLDT.getInBounds(kjt.getJavaType()), t);
                } else {
                    return tt();
                }
            }

    public Term reachableValue(Services services, Term t, KeYJavaType kjt) {
        return reachableValue(services, getBaseHeap(services), t, kjt);
    }

    public Term reachableValue(Services services, ProgramVariable pv) {
        return reachableValue(services, var(pv), pv.getKeYJavaType());
    }

    public Term frame(Services services, Term heapTerm, Map<Term,Term> normalToAtPre, Term mod) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter()
                                       .getHeapLDT()
                                       .getFieldSort();
        
        final Name objVarName   = new Name(newName(services, "o"));
        final Name fieldVarName = new Name(newName(services, "f"));
        final LogicVariable objVar   
        	= new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar 
        	= new LogicVariable(fieldVarName, fieldSort);
        final Term objVarTerm = var(objVar);
        final Term fieldVarTerm = var(fieldVar);
        
        final OpReplacer or = new OpReplacer(normalToAtPre);
        final Term modAtPre = or.replace(mod);
        final Term createdAtPre = or.replace(created(services, heapTerm, objVarTerm));
    
        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
        return all(quantVars,
        	   or(elementOf(services,
                                objVarTerm,
                                fieldVarTerm,
                                modAtPre),
                      and(not(equals(objVarTerm, NULL(services))),
                      not(createdAtPre)),
                      equals(select(services,
                                    Sort.ANY,
                                    heapTerm,
                                    objVarTerm,
                                    fieldVarTerm),
                             select(services,
                                    Sort.ANY,
                                    or.replace(heapTerm),
                                    objVarTerm,
                                    fieldVarTerm))));
    }

    /**
     * Returns the framing condition that the resulting heap is identical (i.e.
     * has the same value in all locations) to the before-heap.
     * 
     * @see #frame(Services, Term, Map, Term)
     */
    public Term frameStrictlyEmpty(Services services, Term heapTerm, Map<Term,Term> normalToAtPre) {
        final Sort objectSort = services.getJavaInfo().objectSort();
        final Sort fieldSort = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSort();
    
        final Name objVarName   = new Name(newName(services, "o"));
        final Name fieldVarName = new Name(newName(services, "f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final Term objVarTerm = var(objVar);
        final Term fieldVarTerm = var(fieldVar);
    
        final OpReplacer or = new OpReplacer(normalToAtPre);
    
        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
        
        return all(quantVars,
                equals(select(services,
                        Sort.ANY,
                        heapTerm,
                        objVarTerm,
                        fieldVarTerm),
                        select(services,
                                Sort.ANY,
                                or.replace(heapTerm),
                                objVarTerm,
                                fieldVarTerm)));
    }

    public Term inv(IServices services, Term h, Term o) {
        return func(services.getJavaInfo().getInv(),
        	    h,
        	    o);
    }

    public Term inv(IServices services, Term o) {
        return inv(services, getBaseHeap(services),  o);
    }

    public Term staticInv(Services services, Term h, KeYJavaType t) {
        return func(services.getJavaInfo().getStaticInv(t), h);
    }

    public Term staticInv(Services services, KeYJavaType t) {
        return func(services.getJavaInfo().getStaticInv(t), getBaseHeap(services));
    }
    
    public Term arrayStore(Services services, Term o, Term i, Term v) {
        return store(services, 
                getBaseHeap(services), 
        	     o, 
        	     func(services.getTypeConverter().getHeapLDT().getArr(), i),
        	     v);
    }        
    

    public Term staticFieldStore(Services services, Function f, Term v) {
	return fieldStore(services, NULL(services), f, v);
    }

    public Term wellFormed(LocationVariable heap, Services services) {
        return wellFormed(var(heap), services);
    }
    



}
