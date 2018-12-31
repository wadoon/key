package genmethod;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import core.ProgramTraceInserterVisitor;
import core.TermVariableNameCollectorVisitor;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;

public abstract class MethodGenerator {
	public static String generateMethodFromKeYFormat(StatementBlock program, Term update, While loop) {
		//FIXME: sind in Update wirklich immer alle relevanten Variablen? Siehe ImmutableList<Goal> openGoals = keyAPI.prove(proof);
		//FIXME: was passiert, wenn darüber schon autoprooft wird, und die Variablen quasi schon älter sind, wurden dann die Updates schon vorher durchgeführt und die Variablen tauchen hier nicht mehr auf?
		// Extrahiere Funktions-Input-Variablen (die die Zuweisung wie elem-update(_x)(x) haben) und extrahiere weitere Variablen, die relevant in der Schleife sind (elem-update(q)(Z(0(#))) & elem-update(r)(x))
		TermVariableNameCollectorVisitor varNameCollector = new TermVariableNameCollectorVisitor();
		update.execPreOrder(varNameCollector);
		
		String returnVariable = extractReturnVariableFromProgram(program);
		
		ProgramTraceInserterVisitor programTraceInserterVisitor = new ProgramTraceInserterVisitor();
		//program.getBody().forEach(s -> s.);
		
		StringBuilder javaCodeBuilder = new StringBuilder();
		StringBuilder inputVariableFromParameterListBuilder = new StringBuilder();
		StringBuilder variableAssignmentBuilder = new StringBuilder();
		StringBuilder functionHeaderBuilder = new StringBuilder();
		StringBuilder beginLoopAddTracesBuilder = new StringBuilder();
		StringBuilder beginLoopArrayListVarStringBuilder = new StringBuilder();
		StringBuilder afterLoopVarDeclarationBuilder = new StringBuilder();
		
		final String packageString = "package genmethod;";
		final String importString = "import java.util.ArrayList;";
		final String classHeader = "public class GeneratedMethod implements IGeneratedMethod {";
		final String parameterName = "inputVariables";
		final String functionType = "GeneratedMethodReturnObject";
		final String returnObject = "generatedMethodReturnObject";
		
		// GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
		String returnObjectDeclaration = functionType + " " + returnObject + " = new " + functionType + "();";
		
		// FIXME: Better Logic
		functionHeaderBuilder.append("public ");
		functionHeaderBuilder.append(functionType);
		functionHeaderBuilder.append(" callGeneratedMethod(ArrayList<Integer> ");
		functionHeaderBuilder.append(parameterName);
		functionHeaderBuilder.append(")");
		
		// Extrahiere input Variables vom visitor
		// und local Variables
		HashMap<String, String> assignmentAndinputVars = new HashMap<String, String>(); // int _x = x
		HashMap<String, String> localVarsAndAssignment = new HashMap<String, String>();
		for (Entry<String, String> e : varNameCollector.variables.entrySet()) {
			// Build Assignments
			variableAssignmentBuilder.append("int ");
			variableAssignmentBuilder.append(e.getKey());
			variableAssignmentBuilder.append(" = ");
			variableAssignmentBuilder.append(e.getValue());
			variableAssignmentBuilder.append(";");
			variableAssignmentBuilder.append(System.lineSeparator());
			
			// Function input Variables start with underscore _
			String variableName = e.getKey().toString();
			if (variableName.startsWith("_")) {
				assignmentAndinputVars.put(e.getKey(), e.getValue()); //care: e.getKey() is _x, not x
			} 
			else {
				localVarsAndAssignment.put(e.getKey(), e.getValue());
			}
		}
		
		// Build assignments like x = inputVariables.get(0) from generic parameter
		int i = 0;
		for (Entry<String, String> e : assignmentAndinputVars.entrySet()) {
			inputVariableFromParameterListBuilder.append("int ");
			inputVariableFromParameterListBuilder.append(e.getValue()); //x
			inputVariableFromParameterListBuilder.append(" = ");
			inputVariableFromParameterListBuilder.append(parameterName);
			inputVariableFromParameterListBuilder.append(".get(");
			inputVariableFromParameterListBuilder.append(i);
			inputVariableFromParameterListBuilder.append(");");
			inputVariableFromParameterListBuilder.append(System.lineSeparator());
			++i;
		}
		
		// Build code like ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
		ArrayList<String> beginLoopVarNames = getVariablesNamesWithPrefix(varNameCollector.variables.keySet(), "beginLoop_");
		ArrayList<String> beginLoopArrayListVarStrings = getArrayListVarStringsFromVars(beginLoopVarNames);
		for (String s : beginLoopArrayListVarStrings) {
			beginLoopArrayListVarStringBuilder.append(s);
			beginLoopArrayListVarStringBuilder.append(System.lineSeparator());
		}
		
		Iterator<String> varNames = varNameCollector.variables.keySet().iterator();
		for (String s : beginLoopVarNames) {
			beginLoopAddTracesBuilder.append(s);
			beginLoopAddTracesBuilder.append(".add(");
			beginLoopAddTracesBuilder.append(varNames.next());
			beginLoopAddTracesBuilder.append(");");
			beginLoopAddTracesBuilder.append(System.lineSeparator());
		}
		
		ArrayList<String> afterLoopVarNames = getVariablesNamesWithPrefix(varNameCollector.variables.keySet(), "afterLoop_");
		Iterator<String> varNames2 = varNameCollector.variables.keySet().iterator();
		for (String s : afterLoopVarNames) {
			afterLoopVarDeclarationBuilder.append("int ");
			afterLoopVarDeclarationBuilder.append(s);
			afterLoopVarDeclarationBuilder.append(" = ");
			afterLoopVarDeclarationBuilder.append(varNames2.next());
			afterLoopVarDeclarationBuilder.append(";");
			afterLoopVarDeclarationBuilder.append(System.lineSeparator());
		}
		
		// Build Code
		javaCodeBuilder.append(packageString);
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(importString);
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
		//Remove leading "{" of StatementBlock to inject variable assignments (done above)
		//javaCodeBuilder.append(program.toSource().replaceAll("^\\{+", ""));
		for (String s : beginLoopArrayListVarStrings) {
			javaCodeBuilder.append(s);
			javaCodeBuilder.append(System.lineSeparator());
		}
		
		
		String loopString = loop.toSource();
		Matcher m = Pattern.compile("while.*(\\{)").matcher(loopString);
		String replacement = "{" +  beginLoopAddTracesBuilder.toString();
		if (m.find()) {
			String injectedInWhile = new StringBuilder(loopString).replace(m.start(1), m.end(1), replacement).toString();
			javaCodeBuilder.append(injectedInWhile);
		} else
			javaCodeBuilder.append(loop.toSource());
		
		
		
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(afterLoopVarDeclarationBuilder.toString());
		javaCodeBuilder.append(buildCodeForReturnObject(returnObject, beginLoopVarNames, afterLoopVarNames, returnVariable));
		javaCodeBuilder.append("return " + returnObject + ";");
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("}");
		// Close Class declaration
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("}");

		return javaCodeBuilder.toString();
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
	
	public static ArrayList<String> getVariablesNamesWithPrefix(Set<String> variables, String prefix) {
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
