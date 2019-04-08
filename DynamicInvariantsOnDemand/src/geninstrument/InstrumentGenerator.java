package geninstrument;

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
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import helperfunctions.HelperFunctions;

public abstract class InstrumentGenerator {
	public static String generateInstrumentFromKeYFormat(While loop, Term update) {
		//FIXME: sind in Update wirklich immer alle relevanten Variablen? Siehe ImmutableList<Goal> openGoals = keyAPI.prove(proof);
		//FIXME: was passiert, wenn dar�ber schon autoprooft wird, und die Variablen quasi schon �lter sind, wurden dann die Updates schon vorher durchgef�hrt und die Variablen tauchen hier nicht mehr auf?
		// Extrahiere Funktions-Input-Variablen (die die Zuweisung wie elem-update(_x)(x) haben) und extrahiere weitere Variablen, die relevant in der Schleife sind (elem-update(q)(Z(0(#))) & elem-update(r)(x))
		TermUpdateVisitor varNameCollector = new TermUpdateVisitor();
		update.execPreOrder(varNameCollector);
		
		GenInstrumentData.getInstance().isInitialized = false;
		
		StringBuilder javaCodeBuilder = new StringBuilder();
		StringBuilder importBuilder = new StringBuilder();
		StringBuilder inputVariableFromParameterListBuilder = new StringBuilder();
		StringBuilder variableAssignmentBuilder = new StringBuilder();
		StringBuilder functionHeaderBuilder = new StringBuilder();
		StringBuilder tracesAddBuilder = new StringBuilder();
		StringBuilder tracesArrayListVarStringBuilder = new StringBuilder();
		
		final String packageString = "package geninstrument;";
		final String classHeader = "public class GenInstrument implements IGenInstrument {";
		final String parameterName = "inputVariables";
		final String functionType = "HashMap<String, ArrayList<Integer>>";
		final String returnObject = "varLoopHeadTraces";
		
		//imports
		importBuilder.append("import java.util.ArrayList;");
		importBuilder.append(System.lineSeparator());
		importBuilder.append("import java.util.HashMap;");
		importBuilder.append(System.lineSeparator());
		
		String returnObjectDeclaration = functionType + " " + returnObject + " = new " + functionType + "();";
		
		// FIXME: Better Logic
		functionHeaderBuilder.append("public ");
		functionHeaderBuilder.append(functionType);
		functionHeaderBuilder.append(" callGenInstrument(ArrayList<Integer> ");
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
		GenInstrumentData.getInstance().inputVars = inputVars;
		GenInstrumentData.getInstance().isInitialized = true;

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
