package de.uka.ilkd.key.testgen.oracle;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.ReflectionClassCreator;
import de.uka.ilkd.key.testgen.TestCaseGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleUnaryTerm.Op;

public class OracleGeneratorNoninterference extends OracleGenerator {

	public OracleGeneratorNoninterference(Services services, ReflectionClassCreator rflCreator, boolean useRFL) {
		super(services, rflCreator, useRFL);
	}
	
	@Override
	public OracleMethod generateOracleMethod(Term term) {
		constants = getConstants(term);
		methodArgs = getMethodArgs(term);
		OracleTerm body = generateNoninterferenceOracle(term, false, true, false);
//		OracleTerm body = generateOracle(term, false); //TODO remove
		return new OracleMethod("testOracle", methodArgs, "return "+body.toString()+";");
	}
	
	@Override
	protected List<OracleVariable> getMethodArgs(Term t){
		System.out.println("right get Method args"); //TODO muessig remove
		
		List<OracleVariable> result = new LinkedList<OracleVariable>();


		Sort allIntSort = createSetSort("Integer");
		Sort allBoolSort = createSetSort("Boolean");
		Sort allObjSort = createSetSort("java.lang.Object");
		Sort oldMapSort = new SortImpl(new Name("Map<Object,Object>"));
		
		OracleVariable allInts = new OracleVariable(TestCaseGenerator.ALL_INTS, allIntSort);
		OracleVariable allBools = new OracleVariable(TestCaseGenerator.ALL_BOOLS, allBoolSort);
		OracleVariable allObj = new OracleVariable(TestCaseGenerator.ALL_OBJECTS, allObjSort);
		OracleVariable oldMap = new OracleVariable(TestCaseGenerator.OLDMap, oldMapSort);
		
		for(Term c : constants){
			result.add(new OracleVariable(c.toString().replaceAll(AT_POST, ""), c.sort()));
			result.add(new OracleVariable(PRE_STRING+c.toString().replaceAll(AT_POST, ""), c.sort()));		
		}

		result.add(allBools);
		result.add(allInts);
		result.add(allObj);		
		result.add(oldMap);
		return result;
	}
	
	//TODO muessig move to new class
	private boolean isAllFieldsEquals(Term term) {
		Operator op = term.op();
		String javaOp = ops.get(op);
		if (javaOp.equals(EQUALS)) {
			Term left = term.sub(0);
			Term right = term.sub(1);
			if (left.op() instanceof Function && right.op() instanceof Function) {
				Function leftFun = (Function) left.op();
				Function rightFun = (Function) right.op();
				if(leftFun.name().toString().equals("allFields") && rightFun.name().toString().equals("allFields")) {
					return true;
				}
				
			}
		}
		return false;
	}	
	
	public OracleTerm generateNoninterferenceOracle(Term term, boolean initialSelect, boolean firstCall, boolean needPrestate) {
		if (firstCall) System.out.println("right oracle generation "); //TODO remove
		
		Operator op = term.op();

		//binary terms
		if(ops.containsKey(op)){
			
			//Equals with allFields (AllFields(a) == AllFields(b))
			if(isAllFieldsEquals(term)) {
				Term left = term.sub(0).sub(0);
				Term right = term.sub(1).sub(0);
				
				String rightSort = left.sort().name().toString();
				String leftSort = right.sort().name().toString();
				OracleMethod method;
				List<OracleTerm> args;
				
				
				//AllFields for Array with same Type? (a[*] == b[*]) // TODO muessig check if allFields without Arrays are necessary
				if(leftSort.endsWith("[]") && leftSort.endsWith("[]") && rightSort.equals(leftSort)) {
				
					method = allFieldsArrayEqualsToMethod(left, right, initialSelect);
					
					oracleMethods.add(method);
					args = new LinkedList<OracleTerm>();
					args.addAll(quantifiedVariables);
					args.addAll(methodArgs);
				} else {
					throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
				}
				
				return new OracleMethodCall(method, args);
			}
			
			
			OracleTerm left = generateNoninterferenceOracle(term.sub(0), initialSelect, false, needPrestate);
			OracleTerm right = generateNoninterferenceOracle(term.sub(1), initialSelect, false, needPrestate);	
			String javaOp = ops.get(op);

			if(javaOp.equals(EQUALS)){
				
				return eq(left, right);
			}
			else if(javaOp.equals(AND)){
				return and(left,right);
			}
			else if(javaOp.equals(OR)){
				return or(left,right);
			}			
			
			return new OracleBinTerm(javaOp,left,right);			
		}//negation
		else if(op == Junctor.NOT){
			OracleTerm sub = generateNoninterferenceOracle(term.sub(0), initialSelect, false, needPrestate);
			if(sub instanceof OracleUnaryTerm){
				OracleUnaryTerm neg = (OracleUnaryTerm) sub;
				return neg.getSub();
			}
			return new OracleUnaryTerm(sub, Op.Neg);
		}
		//true
		else if (op == Junctor.TRUE) {
			return OracleConstant.TRUE;
		}
		//false
		else if (op == Junctor.FALSE) {
			return OracleConstant.FALSE;
		}
		//imp - if imp is outer operation, then left term is in pre state
		else if (op == Junctor.IMP){
			OracleTerm left;
			OracleTerm right;
			if (firstCall) {
				//left term from imp need pre state !!!
				left = generateNoninterferenceOracle(term.sub(0), initialSelect, false, true);
				right = generateNoninterferenceOracle(term.sub(1), initialSelect, false, needPrestate);
			} else {
				left = generateNoninterferenceOracle(term.sub(0), initialSelect, false, needPrestate);
				right = generateNoninterferenceOracle(term.sub(1), initialSelect, false, needPrestate);			
			}
			OracleTerm notLeft = neg(left);
			return new OracleBinTerm(OR, notLeft, right);
		}
		
		
		//quantifiable variable //TODO muessig check if needed
		else if (op instanceof QuantifiableVariable) {			
			QuantifiableVariable qop = (QuantifiableVariable) op;
			if(needPrestate) {
				return new OracleVariable(PRE_STRING+qop.name().toString().replaceAll(AT_POST, ""), qop.sort());
			} else {
				return new OracleVariable(qop.name().toString().replaceAll(AT_POST, ""), qop.sort());	
			}
		}
		//integers
		else if (op == services.getTypeConverter().getIntegerLDT()
		        .getNumberSymbol()) {			
			long num = NumberTranslation.translate(term.sub(0)).longValue();			
			return new OracleConstant(Long.toString(num),term.sort());
		}
		//forall
		else if (op == Quantifier.ALL || op == Quantifier.EX) {
			Sort field = services.getTypeConverter().getHeapLDT().getFieldSort();
			Sort heap = services.getTypeConverter().getHeapLDT().targetSort();
			Sort varSort = term.boundVars().get(0).sort();
			if(varSort.equals(field) || varSort.equals(heap)){
				return OracleConstant.TRUE;
			}
			
			OracleMethod method = createQuantifierMethod(term, initialSelect, firstCall, needPrestate);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			args.addAll(quantifiedVariables);
			args.addAll(methodArgs);
			return new OracleMethodCall(method, args);
		}		
		//if-then-else
		else if(op == IfThenElse.IF_THEN_ELSE){
			OracleMethod method = createIfThenElseMethod(term, initialSelect, firstCall, needPrestate);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			args.addAll(quantifiedVariables);
			args.addAll(methodArgs);
			return new OracleMethodCall(method, args);
		}
		//functions
		else if (op instanceof Function) {
			return translateFunction(term, initialSelect, firstCall, needPrestate);
		}
		//program variables
		else if (op instanceof ProgramVariable){
			ProgramVariable var = (ProgramVariable) op;
			LocationVariable loc = (LocationVariable) var;
			if(needPrestate) {
				// generate name with pre state !
				return new OracleConstant(PRE_STRING+loc.name().toString().replaceAll(AT_POST, ""), loc.sort());
			} else {
				return new OracleConstant(loc.name().toString().replaceAll(AT_POST, ""), loc.sort()); //TODO muessig check if correct and remove if not
			}
		}
				
		else{
			//System.out.println("Could not translate: "+term);
			throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
		}
			
	}
	
	private OracleTerm translateFunction(Term term, boolean initialSelect, boolean firstCall ,boolean needPrestate) {
		System.out.println("right translate function ");//TODO remove
	    Operator op = term.op();
		Function fun = (Function) op;
		String name = fun.name().toString();
		
	    if(isTrueConstant(op)){
	    	return OracleConstant.TRUE;
	    }
	    else if(isFalseConstant(op)){
	    	return OracleConstant.FALSE;
	    }
	    else if(truePredicates.contains(name)){
	    	return OracleConstant.TRUE;
	    }
	    else if(falsePredicates.contains(name)){
	    	return OracleConstant.FALSE;
	    }
	    else if(term.arity() == 0){
	    	return new OracleConstant(name, term.sort());
	    }
	    
	    else if(name.endsWith("select")){
	    	
	    	//System.out.println(term+ " init: "+initialSelect);
	    	
	    	return translateSelect(term, initialSelect, firstCall,needPrestate);	    	
	    }
	    else if(name.equals("arr")){ //TODO muessig check prestate
	    	OracleTerm index = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);	    	
	    	return new OracleConstant("["+index+"]", term.sort());	    	
	    }
	    else if(name.equals("length")){
	    	OracleTerm o = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);
	    	return new OracleConstant(o + ".length", term.sort());
	    }	    
	    else if(name.endsWith("::<inv>")){	 

	    	if(fun instanceof IObserverFunction){
	    		IObserverFunction obs = (IObserverFunction) fun;
	    		
	    		Sort s = obs.getContainerType().getSort();
	    		OracleMethod m;
	    		
	    		if(invariants.containsKey(s)){
	    			m = invariants.get(s);
	    		}
	    		else{
	    			//needed for recursive invariants
	    			m = createDummyInvariant(s);
	    			invariants.put(s, m);
	    			
	    			m = createInvariantMethod(s, initialSelect, firstCall, needPrestate);
	    			invariants.put(s, m);
	    			oracleMethods.add(m);
	    		}
	    		
	    		Term heap = term.sub(0);	    	
		    	OracleTerm heapTerm  = generateNoninterferenceOracle(heap, initialSelect, firstCall, needPrestate);
		    	
		    	Term object = term.sub(1);
		    	OracleTerm objTerm = generateNoninterferenceOracle(object, initialSelect, firstCall, needPrestate);
		    	
		    	if(isPreHeap(heapTerm)){ //delete if pre is already set with "needPrestate"
		    		if(!objTerm.toString().startsWith(PRE_STRING)){	
		    			prestateTerms.add(objTerm.toString());		    			
		    			objTerm = new OracleConstant(PRE_STRING+object.toString(), object.sort());		    			
		    		}
		    	}	    		
	    		
	    		List<OracleTerm> args = new LinkedList<OracleTerm>();
	    		args.add(objTerm);
	    		args.addAll(quantifiedVariables);
	    		args.addAll(methodArgs);
	    		
	    		return new OracleMethodCall(m, args);
	    	}
	    }
	    else if (name.endsWith("::instance")){

	    	if(fun instanceof SortDependingFunction){
	    		SortDependingFunction sdf  = (SortDependingFunction) fun;
	    		Sort s = sdf.getSortDependingOn();
	    		
	    		
	    		OracleTerm arg = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);
	    		OracleType type = new OracleType(s);
	    		
	    		return new OracleBinTerm("instanceof", arg, type);
	    		
	    		
	    	}
	    	
	    	
	    }
	    else if(op instanceof ProgramMethod){
	    	return translateQuery(term, initialSelect, op, firstCall, needPrestate); 
	    	
	    	
	    }
	    else if(name.equals("javaUnaryMinusInt")){
	    	OracleTerm sub = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);
	    	return new OracleUnaryTerm(sub, Op.Minus);
	    }
	    
	    
	    else if (name.equals("newObjectsIsomorphic")) {
	    	OracleMethod method = createIsomorphicOracleMethod(term, initialSelect);
			oracleMethods.add(method);
			List<OracleTerm> args = new LinkedList<OracleTerm>();
			args.addAll(quantifiedVariables);
			args.addAll(methodArgs);
			return new OracleMethodCall(method, args);
	    }
	    throw new RuntimeException("Unsupported function found: "+name+ " of type "+fun.getClass().getName());	}
	
	private OracleTerm translateQuery(Term term, boolean initialSelect,
			Operator op, boolean firstCall, boolean needPrestate) {
		
		ProgramMethod pm = (ProgramMethod) op;		
		OracleMethod m = createDummyOracleMethod(pm);
		
		
		List<OracleTerm> params = new LinkedList<OracleTerm>();
		
		for(int i = pm.isStatic()?1:2 ; i < term.subs().size(); i++){
			OracleTerm param = generateNoninterferenceOracle(term.subs().get(i), initialSelect, firstCall, needPrestate);
			params.add(param);
		}
		
		System.out.print("pm="+pm.name()+" ");
        for(int i = 0; i < term.arity(); i++){
            System.out.print("(i="+i+"):"+term.sub(i)+" ");
        }
		
		if(pm.isStatic()){
		    System.out.println(" isstatic ");
		    return new OracleMethodCall(m,params);
		}else{
		    OracleTerm caller = generateNoninterferenceOracle(term.sub(1),false /*TODO: what does this parameter mean?*/, firstCall, needPrestate);
            System.out.println(" non-static caller="+caller);
		    return new OracleMethodCall(m,params, caller);
		}
	}
	
	private OracleTerm translateSelect(Term term, boolean initialSelect, boolean firstCall,boolean needPrestate) {
		Term heap = term.sub(0);	    	
		OracleTerm heapTerm  = generateNoninterferenceOracle(heap, true, firstCall, needPrestate);	   	
		
		Term object = term.sub(1);	
		
		OracleTerm objTerm = generateNoninterferenceOracle(object, true, firstCall, needPrestate);
		
		
		
		Term field = term.sub(2);
		OracleTerm fldTerm = generateNoninterferenceOracle(field, true, firstCall, needPrestate);
		String fieldName = fldTerm.toString();
		fieldName = fieldName.substring(fieldName.lastIndexOf(":")+1, fieldName.length());
		fieldName = fieldName.replace("$", "");
		
		String value;
		
		value = createLocationString(heapTerm, objTerm, fieldName, object.sort(), term.sort(), initialSelect);		
		
		if(!initialSelect && isPreHeap(heapTerm)){
			if(term.sort().extendsTrans(services.getJavaInfo().getJavaLangObject().getSort())){
				return new OracleConstant(TestCaseGenerator.OLDMap+".get("+value+")", term.sort());
			}
		}		
		
		return new OracleConstant(value, term.sort());
	}
	
	//TODO muessig move to new class -> remove
	private String[] getObjNamesFromList(Term t, int size) {
		int i = 0;
		String[] names = new String[size];
		for (Term a : t.subs()) {
			names[i] = a.toString().replaceAll("AtPost", "");
			i++;
		}
		return names;
	}
	
	//TODO muessig move to new class -> remove
	private String checkPreString(String[] names) {
		String checkPreOne = "";
		for (int i = 0; i < names.length-1; i++) {
			checkPreOne = checkPreOne + PRE_STRING+names[i]+EQUALS+" null "+ AND;
		}
		return checkPreOne+PRE_STRING+names[names.length-1]+EQUALS+" null";
	}
		
	//TODO muessig move to new class -> remove
	private String checkTypeString(String[] namesA, String[] namesB) {
		String result = "";
		for(int i = 0; i < namesA.length-1; i++) {
			result = result + namesA[i]+".class " + EQUALS + " " +namesB[i]+".class &&";
		}
		return result + namesA[namesA.length-1]+".class " + EQUALS + " " +namesB[namesB.length-1]+".class";
	}
		
		
	//compare the objects. Same Type, Same fileds with same values
		//TODO muessig implement with needPrestate !!!!!
	private OracleMethod createIsomorphicOracleMethod(Term term, boolean initialSelect) {
		
		String result = "";
		String methodName = generateMethodName();
		String tab = TestCaseGenerator.TAB;
		Term objectListA = term.sub(0);
		Term objectListB = term.sub(2);
		
		
		int listSize = objectListA.subs().size();
		if (listSize != objectListB.subs().size()) {
			throw new RuntimeException("Could not translate oracle for: "+term+" of type "+term.op());
		}
		
		//all objects in the list as String
		String[] objANames = getObjNamesFromList(objectListA, listSize);
		String[] objBNames = getObjNamesFromList(objectListB, listSize);
		
		String objectsA = "{";
		String objectsB = "{";
		for (int i = 0; i < listSize-1; i++) {
			objectsA = objectsA + objANames[i] + ",";
			objectsB = objectsB + objBNames[i] + ",";
		}
		objectsA = objectsA + objANames[listSize-1]+"}";
		objectsB = objectsB + objBNames[listSize-1]+"}";
			
		String objectArrays = "\n"+tab+tab+"Object[] objectsA = "+objectsA+";"
								+"\n"+tab+tab+"Objects objectsB = "+objectsB+";";
		
		result = result + objectArrays;
		
		//list of objects
		//check if exists in prestate
		String checkPreOne = checkPreString(objANames);
		String checkPreSec = checkPreString(objBNames);
		String checkIfNew =
				"\n"+tab+tab+"//check if objects new "
				+"\n"+tab+tab+"if(!("+checkPreOne + "&&" + checkPreSec+")) {"
						+"\n"+tab+tab+tab+"return false;"
						+"\n"+tab+tab+"}";
		
		result = result + checkIfNew;
		
		
		//check the type of obj in list with .class
		String compareTypes = checkTypeString(objANames, objBNames);		
		String checkType =
				"\n"+tab+tab+"//check object types"
				+"\n"+tab+tab+"if(!("+compareTypes+")) {"
					+"\n"+tab+tab+tab+"return false;"
					+"\n"+tab+tab+"}";
			
		
		result = result + checkType;
		    
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(quantifiedVariables);
		args.addAll(methodArgs);
		
		
		return new OracleMethod(methodName, args, result);
	}
	
	private OracleMethod allFieldsArrayEqualsToMethod(Term leftTerm, Term rightTerm, boolean initialSelect) {
		
		
		String methodName = generateMethodName();
			
		String tab = TestCaseGenerator.TAB;
		String body = 
				"\n" + tab + "if("+leftTerm+".length"+EQUALS+rightTerm+".length"+" ) {"
				+ "\n"+tab+tab+"for("+"int"+" "+"i"+" : "+TestCaseGenerator.ALL_INTS+"){"
				+ "\n"+tab+tab+tab+"if("+"0 <= i"+ " && " + "i < "+ leftTerm+ ".length"+ " && " +"!("+leftTerm+"[i]"+EQUALS+rightTerm+"[i]"+")){"
				+ "\n"+tab+tab+tab+tab+"return false;"
				+ "\n"+tab+tab+tab+"}"
				+ "\n"+tab+tab+"}"
				+ "\n"+tab+"} else {"
				+ "\n"+tab+tab+"return false;"
				+ "\n"+tab+"}"
				+ "\n"+tab+"return true;";
		    
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(quantifiedVariables);
		args.addAll(methodArgs);

		return new OracleMethod(methodName, args, body);
		
	}
	
	private OracleMethod createInvariantMethod(Sort s, boolean initialSelect, boolean firstCall, boolean needPrestate){		
		
		String methodName = getSortInvName(s);
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		OracleVariable o = new OracleVariable("o", s);		
		args.add(o);
		args.addAll(methodArgs);
		OracleInvariantTranslator oit = new OracleInvariantTranslator(services);
		Term t = oit.getInvariantTerm(s);
		
		OracleTerm invTerm = generateNoninterferenceOracle(t, initialSelect, firstCall, needPrestate);
		
		String body = "return "+invTerm.toString()+";";
		
		return new OracleMethod(methodName, args, body);
		
		
		
		
	}
	
	private OracleMethod createIfThenElseMethod(Term term, boolean initialSelect, boolean firstCall, boolean needPrestate){
			
		String methodName = generateMethodName();
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(methodArgs);
		OracleTerm cond = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);
		OracleTerm trueCase = generateNoninterferenceOracle(term.sub(1), initialSelect, firstCall, needPrestate);
		OracleTerm falseCase = generateNoninterferenceOracle(term.sub(2), initialSelect, firstCall, needPrestate);
		
		String body = "if("+cond+"){"
				+ "\n   return "+trueCase+";"
				+ "\n}else{"
				+ "\n   return "+falseCase+";"
				+ "\n}";
		
		return new OracleMethod(methodName, args, body, term.sort());		
		
	}	
	private OracleMethod createQuantifierMethod(Term term, boolean initialSelect, boolean firstCall, boolean needPrestate){		
		String methodName = generateMethodName();
		ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		QuantifiableVariable qv = vars.get(0);
		OracleVariable var = new OracleVariable(qv.name().toString(), qv.sort());
				
		String setName = getSetName(qv.sort());
		
		quantifiedVariables.add(var);
		OracleTerm sub = generateNoninterferenceOracle(term.sub(0), initialSelect, firstCall, needPrestate);
		quantifiedVariables.remove(var);
		
		OracleUnaryTerm neg = new OracleUnaryTerm(sub,Op.Neg);
		
		String body;
		if(term.op() == Quantifier.ALL){
			body = createForallBody(qv, setName, neg);
		}
		else if(term.op() == Quantifier.EX){
			body = createExistsBody(qv, setName, sub);
		}
		else{
			throw new RuntimeException("This is not a quantifier: "+term);
		}		
		
		
		List<OracleVariable> args = new LinkedList<OracleVariable>();
		args.addAll(quantifiedVariables);
		args.addAll(methodArgs);
		
		
		return new OracleMethod(methodName, args, body);		
	}
	
}
