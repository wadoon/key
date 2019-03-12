package genmethod;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import core.TermUpdateVisitor;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import helperfunctions.HelperFunctions;

public abstract class MethodGenerator {
	public static String generateMethodFromKeYFormat(StatementBlock program, Term update, While loop) {
		//FIXME: sind in Update wirklich immer alle relevanten Variablen? Siehe ImmutableList<Goal> openGoals = keyAPI.prove(proof);
		//FIXME: was passiert, wenn dar�ber schon autoprooft wird, und die Variablen quasi schon �lter sind, wurden dann die Updates schon vorher durchgef�hrt und die Variablen tauchen hier nicht mehr auf?
		// Extrahiere Funktions-Input-Variablen (die die Zuweisung wie elem-update(_x)(x) haben) und extrahiere weitere Variablen, die relevant in der Schleife sind (elem-update(q)(Z(0(#))) & elem-update(r)(x))
		TermUpdateVisitor varNameCollector = new TermUpdateVisitor();
		update.execPreOrder(varNameCollector);
		
		//String returnVariable = extractReturnVariableFromProgram(program);
		
		GenMethodData.getInstance().isInitialized = false;
		
		StringBuilder javaCodeBuilder = new StringBuilder();
		StringBuilder importBuilder = new StringBuilder();
		StringBuilder inputVariableFromParameterListBuilder = new StringBuilder();
		StringBuilder variableAssignmentBuilder = new StringBuilder();
		StringBuilder functionHeaderBuilder = new StringBuilder();
		StringBuilder tracesAddBuilder = new StringBuilder();
		StringBuilder tracesArrayListVarStringBuilder = new StringBuilder();
		StringBuilder afterLoopVarDeclarationBuilder = new StringBuilder();
		
		final String packageString = "package genmethod;";
		final String classHeader = "public class GeneratedMethod implements IGeneratedMethod {";
		final String parameterName = "inputVariables";
		final String functionType = "HashMap<String, ArrayList<Integer>>";
		final String returnObject = "varLoopHeadTraces";
		
		//imports
		importBuilder.append("import java.util.ArrayList;");
		importBuilder.append(System.lineSeparator());
		importBuilder.append("import java.util.HashMap;");
		importBuilder.append(System.lineSeparator());
		
		// GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
		String returnObjectDeclaration = functionType + " " + returnObject + " = new " + functionType + "();";
		
		// FIXME: Better Logic
		functionHeaderBuilder.append("public ");
		functionHeaderBuilder.append(functionType);
		functionHeaderBuilder.append(" callGeneratedMethod(ArrayList<Integer> ");
		functionHeaderBuilder.append(parameterName);
		functionHeaderBuilder.append(")");
		
		// Extrahiere input Variables vom visitor & build assignments
		LinkedHashSet<String> inputVars = new LinkedHashSet<String>(); // int _x = x
		LinkedHashSet<String> allVars = new LinkedHashSet<String>();
		for (Entry<String, String> e : varNameCollector.assignmentsLHS_RHS.entrySet()) {
			String lhs = e.getKey();
			String rhs = e.getValue();
			
			allVars.add(lhs);
			
			// Build Assignments
			variableAssignmentBuilder.append("int ");
			variableAssignmentBuilder.append(lhs);
			variableAssignmentBuilder.append(" = ");
			variableAssignmentBuilder.append(rhs);
			variableAssignmentBuilder.append(";");
			variableAssignmentBuilder.append(System.lineSeparator());
			
			// Right hand side must be on a Left hand side assignment, else it is an input Var
			if (!HelperFunctions.isInteger(rhs) && !varNameCollector.assignmentsLHS_RHS.containsKey(rhs)) {
				inputVars.add(rhs);
				allVars.add(rhs);
			} 
		}
		
		// Build assignments like int x = inputVariables.get(0)
		int i = 0;
		for (String inputVar : inputVars) {
			inputVariableFromParameterListBuilder.append("int ");
			inputVariableFromParameterListBuilder.append(inputVar); //x
			inputVariableFromParameterListBuilder.append(" = ");
			inputVariableFromParameterListBuilder.append(parameterName);
			inputVariableFromParameterListBuilder.append(".get(");
			inputVariableFromParameterListBuilder.append(i);
			inputVariableFromParameterListBuilder.append(");");
			inputVariableFromParameterListBuilder.append(System.lineSeparator());
			++i;
		}
		
		// Build code like ArrayList<Integer> traces__x = new ArrayList<Integer>();
		ArrayList<String> traces = getVariablesNamesWithPrefix(allVars, "traces_");
		ArrayList<String> tracesArrayListsStrings = getArrayListVarStringsFromVars(traces);
		for (String s : tracesArrayListsStrings) {
			tracesArrayListVarStringBuilder.append(s);
			tracesArrayListVarStringBuilder.append(System.lineSeparator());
		}
		
		ArrayList<String> hashMapPuts = getHashMapPuts(returnObject, allVars, traces);
		
		Iterator<String> varNames = allVars.iterator();
		for (String s : traces) {
			tracesAddBuilder.append(s);
			tracesAddBuilder.append(".add(");
			tracesAddBuilder.append(varNames.next());
			tracesAddBuilder.append(");");
			tracesAddBuilder.append(System.lineSeparator());
		}
		
//		ArrayList<String> afterLoopVarNames = getVariablesNamesWithPrefix(varNameCollector.variables.keySet(), "afterLoop_");
//		Iterator<String> varNames2 = varNameCollector.variables.keySet().iterator();
//		for (String s : afterLoopVarNames) {
//			afterLoopVarDeclarationBuilder.append("int ");
//			afterLoopVarDeclarationBuilder.append(s);
//			afterLoopVarDeclarationBuilder.append(" = ");
//			afterLoopVarDeclarationBuilder.append(varNames2.next());
//			afterLoopVarDeclarationBuilder.append(";");
//			afterLoopVarDeclarationBuilder.append(System.lineSeparator());
//		}
		
		// Build Code
		javaCodeBuilder.append(packageString);
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(importBuilder.toString());
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(classHeader);
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(functionHeaderBuilder.toString());
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("{");
		javaCodeBuilder.append(System.lineSeparator());
		//   Function Body
		javaCodeBuilder.append(returnObjectDeclaration);
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(inputVariableFromParameterListBuilder.toString());
		javaCodeBuilder.append(variableAssignmentBuilder.toString());
		//Remove leading "{" (done above) of StatementBlock to inject variable assignments 
		//javaCodeBuilder.append(program.toSource().replaceAll("^\\{+", ""));
		for (String s : tracesArrayListsStrings) {
			javaCodeBuilder.append(s);
			javaCodeBuilder.append(System.lineSeparator());
		}
		for (String s : hashMapPuts) {
			javaCodeBuilder.append(s);
			javaCodeBuilder.append(System.lineSeparator());
		}
		
		
		String loopString = loop.toSource();
		//Pattern: match non greedy (first loop), { is group 1, rest 0
		Matcher m = Pattern.compile("while\\s*\\((?:.+?)(?=\\{)(\\{)").matcher(loopString);
		//Matcher m = Pattern.compile("while.*(\\{)").matcher(loopString);
		// Replace { with { and injected code
		String replacement = "{" +  tracesAddBuilder.toString();
		if (m.find()) {
			//replace { with injected code
			String injectedInWhile = new StringBuilder(loopString).replace(m.start(1), m.end(1), replacement).toString();
			javaCodeBuilder.append(injectedInWhile);
		} else
			javaCodeBuilder.append(loop.toSource());
		
		
		
		javaCodeBuilder.append(System.lineSeparator());
//		javaCodeBuilder.append(afterLoopVarDeclarationBuilder.toString());
//		javaCodeBuilder.append(buildCodeForReturnObject(returnObject, vars, afterLoopVarNames, returnVariable));
		javaCodeBuilder.append("return " + returnObject + ";");
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("}");
		// Close Class declaration
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("}");
		
		// Store information about the generated method (e.g. for testgen)
		GenMethodData.getInstance().inputVars = inputVars;
		GenMethodData.getInstance().isInitialized = true;

		return javaCodeBuilder.toString();
	}
	
	private static ArrayList<String> getHashMapPuts(String hashMapVarName, LinkedHashSet<String> varNames, ArrayList<String> tracesNames) {
		ArrayList<String> hashMapPuts = new ArrayList<String>();
		
		StringBuilder hashMapPutsBuilder = new StringBuilder();
		Iterator<String> tracesNamesIt = tracesNames.iterator();
		for (String var : varNames) {
			hashMapPutsBuilder.append(hashMapVarName);
			hashMapPutsBuilder.append(".put(");
			hashMapPutsBuilder.append("\"" + var + "\"");
			hashMapPutsBuilder.append(",");
			hashMapPutsBuilder.append(tracesNamesIt.next());
			hashMapPutsBuilder.append(");");
			hashMapPuts.add(hashMapPutsBuilder.toString());
			//Clear Builder for next var
			hashMapPutsBuilder.setLength(0);
		}

		return hashMapPuts;
	}
	
	private static String buildCodeForReturnObject(String returnObject, ArrayList<String> beginLoopVarNames, ArrayList<String> afterLoopVarNames, String returnVariable) {
		StringBuilder code = new StringBuilder();
		
     	//Set beginLoop Variables in object
     	String beginLoopTracesAssignment = returnObject + ".beginLoopTraces.add";
		for (String beginLoopVar : beginLoopVarNames) {
			code.append(beginLoopTracesAssignment);
			code.append("(");
			code.append(beginLoopVar);
			code.append(");");
			code.append(System.lineSeparator());
		}
		
		//Set afterLoop Variables in object
     	String afterLoopTracesAssignment = returnObject + ".afterLoopTraces.add";
		for (String afterLoopVar : afterLoopVarNames) {
			code.append(afterLoopTracesAssignment);
			code.append("(");
			code.append(afterLoopVar);
			code.append(");");
			code.append(System.lineSeparator());
		}
		
		//Set original return Value in object
		code.append(returnObject + ".originalReturnValue = " + returnVariable + ";");
		code.append(System.lineSeparator());
		
		return code.toString();
	}

	public static String extractReturnVariableFromProgram(StatementBlock program) {
		String line = program.toSource();
		//FIXME maybe more/less than 2 blanks
		String pattern1 = "return  ";
		String pattern2 = ";";
		
		Pattern p = Pattern.compile(Pattern.quote(pattern1) + "(.*?)" + Pattern.quote(pattern2));
		Matcher m = p.matcher(line);
		if (m.find())
			return m.group(1);
		else
			return null;
	}
	
	public static ArrayList<String> getVariablesNamesWithPrefix(LinkedHashSet<String> variables, String prefix) {
		ArrayList<String> varNames = new ArrayList<String>();
		StringBuilder variablesNameBuilder = new StringBuilder();
		for (String var : variables) {
			variablesNameBuilder.append(prefix);
			variablesNameBuilder.append(var);
			//Add ArrayListVarStrings for this variable to the returned List
			varNames.add(variablesNameBuilder.toString());
			//Clear Builder for next var
			variablesNameBuilder.setLength(0);
		}
		return varNames;
	}
	
	public static ArrayList<String> getArrayListVarStringsFromVars(ArrayList<String> variables) {
		// Example: Returns for variables(beginLoop_x,beginLoop_y): ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
		//										                    ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
		ArrayList<String> arrayListVarStrings = new ArrayList<String>();
		final String BEGIN_DECLARATION = "ArrayList<Integer> ";
		final String END_DECLARATION = " = new ArrayList<Integer>();";
		
		StringBuilder arrayListVarStringBuilder = new StringBuilder();
		for (String var : variables) {
			arrayListVarStringBuilder.append(BEGIN_DECLARATION);
			arrayListVarStringBuilder.append(var);
			arrayListVarStringBuilder.append(END_DECLARATION);
			
			//Add ArrayListVarStrings for this variable to the returned List
			arrayListVarStrings.add(arrayListVarStringBuilder.toString());
			//Clear Builder for next var
			arrayListVarStringBuilder.setLength(0);
		}
		
		return arrayListVarStrings;
	}
}
