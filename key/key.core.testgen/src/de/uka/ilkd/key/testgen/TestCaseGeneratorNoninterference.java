package de.uka.ilkd.key.testgen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.metaconstruct.IsStatic;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.testgen.oracle.OracleGeneratorNoninterference;
import de.uka.ilkd.key.testgen.oracle.OracleMethod;
import de.uka.ilkd.key.testgen.oracle.OracleMethodCall;

public class TestCaseGeneratorNoninterference extends TestCaseGenerator {
	
	public static final String A_EXECUTION = "_A";
	public static final String B_EXECUTION = "_B";

	public TestCaseGeneratorNoninterference(Proof proof) {
		super(proof);
	}
	
	@Override
	protected String getOracleAssertion(List<OracleMethod> oracleMethods) {
		Term postcondition = info.getPostCondition();
		OracleMethod oracle = oracleGenerator.generateOracleMethod(postcondition);

		OracleMethodCall oracleCall = new OracleMethodCall(oracle, oracle.getArgs());

		oracleMethods.add(oracle);
		oracleMethods.addAll(oracleGenerator.getOracleMethods());
		return "assertTrue("+oracleCall.toString().replaceAll("AtPost", "")+");";
	}
	
	/**
	 * check if variable is post variable (for information flow test)
	 * @param c
	 * @return
	 * @author Muessig
	 */
	private boolean isPostName(String c) {
		if(c.contains("AtPost")) {
			return true;
		}
		else {
			return false;
		}
	}
	
	private boolean isPreName(String c) {
		if(c.contains("AtPre")) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/**
	 * returns the name Prefix (execution A or B) for a heap
	 * @param heap
	 * @return String constant _A or _B
	 * @author Muessig
	 */
	private String getExecutionName(String s) {
		
		if (s.contains(A_EXECUTION)) {
			return A_EXECUTION;
		}
		if (s.contains(B_EXECUTION)) {
			return B_EXECUTION;
		}
		return "";
	}
		
	private String createObjSet(List<Heap> heaps) {
		StringBuffer res = new StringBuffer();
			
		res.append(TAB+"Set<Object> "+ALL_OBJECTS +"= new HashSet<Object>();" + NEW_LINE);
			
		//create objects for HeapAtPre_A, HeapAtPre_B
		for (Heap h : heaps) {
			for(ObjectVal o : h.getObjects()){
				String name = o.getName();
				if(name.equals("#o0")){
					continue;
				}
				name = name+getExecutionName(h.getName());
				name = name.replace("#", "_");
				res.append(TAB+ALL_OBJECTS+".add("+name+");" + NEW_LINE);
//				res.append(TAB+ALL_OBJECTS+".add("+getPreName(name)+");" + NEW_LINE);

			}		
		}
		return res.toString();	
	}
	
	@Override
    protected String getRemainingConstants(Collection<String> existingConstants, Collection<Term> newConstants) {
    	String result = "";
    	List<String> constantAlreadyInit= new ArrayList<String>();
    	for(Term c : newConstants) {
    		//filter post variables
    		if (isPostName(c.toString())) {
    			continue;
    		}
    		if(!existingConstants.contains(c.toString())){
				String init = "null";
				if(c.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())){
					init = "0";
				}
				else if(c.sort().equals(services.getTypeConverter().getBooleanLDT().targetSort())){
					init = "false";
				}

				result += NEW_LINE +TAB+ NULLABLE+ " "+ getSafeType(c.sort()) + " " + c + " = " + init + ";";
				
			}
    	}
    	return result;
    }
	
	@Override
	protected void createTestCaseBody(StringBuffer testMethod, Model m ,Map<String, Sort> typeInfMap, String oracleMethodCall) {
		
		m.removeUnnecessaryObjects();
		
		//collect Pre Heaps for execution A/B
		List<Heap> heaps = new ArrayList<Heap>();
		for (final Heap h : m.getHeaps()) {
			if (isPreName(h.getName())) {
				heaps.add(h);
			}
		}
		
		String[] codes = ((NoninterferenceProofInfo) info).getCodeNoninterference();//Sorry for downcast 
		
		Set<Term> vars = new HashSet<Term>();
		info.getProgramVariables(info.getPO(), vars);   
		testMethod.append(TAB+"//Other variables" + getRemainingConstants(m.getConstants().keySet(), vars) + NEW_LINE+ NEW_LINE);
		
		//create preamble and method execution for execution A
		for (Heap heap : heaps) {
			if (getExecutionName(heap.getName()).equals(A_EXECUTION)){
				testMethod
				.append("   //Test preamble for execution "+ "A" + ": creating objects and intializing test data"
						+ generateTestCaseNoninterference(m, heap, typeInfMap) + NEW_LINE + NEW_LINE);
				
				testMethod.append("   //Calling the method under test   " + NEW_LINE + codes[0] + NEW_LINE);
				
			}
		}
		
		//create preamble and method execution for execution B
		for (Heap heap : heaps) {
			if (getExecutionName(heap.getName()).equals(B_EXECUTION)){
				testMethod
				.append("   //Test preamble for execution "+ "B" + ": creating objects and intializing test data"
						+ generateTestCaseNoninterference(m, heap, typeInfMap) + NEW_LINE + NEW_LINE);
				
				testMethod.append("   //Calling the method under test   " + NEW_LINE + codes[1] + NEW_LINE);
				
			}
		}
		//help data for oracle method
		testMethod.append(NEW_LINE);
		testMethod.append(createBoolSet() + NEW_LINE);
		testMethod.append(createIntSet() + NEW_LINE);
		testMethod.append(createObjSet(heaps) + NEW_LINE);	
		
		//append oracleMethodCall
		testMethod.append("   //calling the test oracle" + NEW_LINE+TAB+oracleMethodCall + NEW_LINE);
	}
	
	
	private String generateTestCaseNoninterference(Model m, Heap heap, Map<String, Sort> typeInfMap) {
//		m.removeUnnecessaryObjects(); //TODO restore this if necessary
//		Set<String> objects = new HashSet<String>();
		
		final List<Assignment> assignments = new LinkedList<Assignment>();
		final StringBuffer result = new StringBuffer();
	
		if (heap != null) {
			//create Objects for heap
			for (final ObjectVal o : heap.getObjects()) {
				if (o.getName().equals("#o0")) {
					continue;
				}
					
				final String type = getSafeType(o.getSort());
				String right;
				if (type.endsWith("[]")) {
					right = "new " + type.substring(0, type.length() - 2) + "["
							+ o.getLength() + "]";
				}else if(o.getSort() == null || o.getSort().toString().equals("Null")){
					right = "null";
				}else {
					if(useRFL){
						right = "RFL.new"+ReflectionClassCreator.cleanTypeName(type)+"()";
						rflCreator.addSort(type);
					}else
						right = "new " + type + "()";
				}
				String objName = createObjectName(o)+getExecutionName(heap.getName());

				assignments.add(new Assignment(type, objName, right));
					
					
			}
			// init constants
				
			for (final String c : m.getConstants().keySet()) {
				if (c.equals("self") || isPostName(c)) { //self and post constants not needed
					continue;
				}
				String exName = getExecutionName(c);
				String val = m.getConstants().get(c);
					
				if (filterVal(val) && !c.equals("null") && (exName == getExecutionName(heap.getName().toString()))) {
					boolean isObject = false;
					String type = "int";
					String declType = "int";
					if (val.equals("true") || val.equals("false")) {
						type = "boolean";
					} else if (val.startsWith("#o")) {
					    isObject = true;
					    type = this.inferSort(typeInfMap, c);
		                   
					}
					if(isObject){
		                declType = NULLABLE +" "+type;
					}
					else{
						declType = type;				    
					}
						
					val = translateValueExpression(val);
					if (isObject && !val.equals("null")) { 
						
						//if the constant name doesn't include the Execution A or B do nothing
						if (exName.equals("")) {
	
						} else {
							val = val+exName;
							assignments.add(new Assignment(declType, c, "("+type+")"+val));
						}
					}
					else {
						val = translateValueExpression(val);
						assignments.add(new Assignment(declType, c, "("+type+")"+val));
					}
				}
			}
			// init fields
			if (heap != null) {
				for (final ObjectVal o : heap.getObjects()) {
					if (o.getName().equals("#o0") || o.getSort().name().toString().endsWith("Exception")) {
						continue;
					}
					final String receiverObject = createObjectName(o)+getExecutionName(heap.getName());
					for (final String f : o.getFieldvalues().keySet()) {
							if (f.contains("<") || f.contains(">")) {
								continue;
							}
								
							String fieldName = f.substring(f.lastIndexOf(":") + 1);
							fieldName = fieldName.replace("|", "");
							String val = o.getFieldvalues().get(f);
							//final String vType = getTypeOfValue(heap, m, val);
			                   String fieldName2 = f.replace("|","");
							final String vType = this.inferSort(typeInfMap, fieldName2); //getTypeOfValue(heap, m, val);
							rflCreator.addSort(vType); //possible bug if vType represents an abstract type or an interface. See: getSafeType.
							boolean fieldisObject = false;
							if (val.startsWith("#o")) {
								fieldisObject = true;
							}
							val = translateValueExpression(val);
							final String rcObjType = getSafeType(o.getSort());
							
							if (fieldisObject && !val.equals("null")) {
								assignments
								.add(new Assignment(new RefEx(rcObjType,receiverObject,vType,fieldName), "("+vType+")"+val+getExecutionName(heap.getName())));
							} else {
								assignments
								.add(new Assignment(new RefEx(rcObjType,receiverObject,vType,fieldName), "("+vType+")"+val));
							}
			
					}
					if (o.getSort() != null
							&& o.getSort().name().toString().endsWith("[]")) {
										String safeType = getSafeType(o.getSort());
						String elementType = safeType.substring(0, safeType.length()-2);
						rflCreator.addSort(safeType);					
						for (int i = 0; i < o.getLength(); i++) {
							final String fieldName = "[" + i + "]";
							String val = o.getArrayValue(i);
							val = translateValueExpression(val);
							assignments.add(new Assignment(receiverObject + fieldName, "("+elementType+")"+val));
							
						
						}
					}
				}
			}
			
			for (final Assignment a : assignments) {
				result.append(NEW_LINE + "   ");
				result.append(a.toString(useRFL));
			}
		}
		
		return result.toString();
		
	}
		
}
