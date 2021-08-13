package de.uka.ilkd.key.loopinvgen;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;

public class TestPredicateConstruction {

	private final TermFactory tf;
	private final TermBuilder tb;
	private final NamespaceSet nss;
	private final Services services;

	private String pathToTestKeYFile = "C:\\Users\\Asma\\git\\LIG_3\\key\\key\\key.core\\src\\de\\uka\\ilkd\\key\\loopinvgen\\test.key";

	TestPredicateConstruction() {
		services = HelperClassParsingTests.createServices(new File(pathToTestKeYFile));
		tb = services.getTermBuilder();
		tf = tb.tf();
		nss = services.getNamespaces();
	}

	private KeYParserF stringDeclParser(String s) {
		// fills namespaces
		new Recoder2KeY(services, nss).parseSpecialClasses();
		return new KeYParserF(ParserMode.DECLARATION,
				new KeYLexerF(s, "No file. Call of parser from " + this.getClass().getSimpleName()), services, nss);
	}

	public void parseDecls(String s) throws RecognitionException {
		KeYParserF stringDeclParser = stringDeclParser(s);
		stringDeclParser.decls();
	}

	public Term parseProblem(String s) {
		try {
			new Recoder2KeY(services, nss).parseSpecialClasses();
			KeYLexerF lexer = new KeYLexerF(s, "No file. Call of parser from " + this.getClass().getSimpleName());
			return new KeYParserF(ParserMode.PROBLEM, lexer, new ParserConfig(services, nss),
					new ParserConfig(services, nss), null, ImmutableSLList.<Taclet>nil()).problem();
		} catch (Exception e) {
			StringWriter sw = new StringWriter();
			PrintWriter pw = new PrintWriter(sw);
			e.printStackTrace(pw);
			throw new RuntimeException("Exc while Parsing:\n" + sw);
		}
	}

	protected KeYLexerF getLexer(String s) {
		return new KeYLexerF(s, "No file. Call of parser from parser/" + getClass().getSimpleName());
	}

	protected KeYParserF getParser(String s) {
		Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());
		
		return new KeYParserF(ParserMode.TERM, getLexer(s), r2k, services, nss, new AbbrevMap());
	}

	public Term parse(String s) throws Exception {
		return getParser(s).term();
	}

	public Term parseFormula(String s) {
		try {
			return getParser(s).formula();
		} catch (Exception e) {
			StringWriter sw = new StringWriter();
			PrintWriter pw = new PrintWriter(sw);
			e.printStackTrace(pw);
			throw new RuntimeException("Exc while Parsing:\n" + sw);
		}
	}

//	public void testCase1() {
//		Term formula;
//				
//		try {
//			formula = parse("{i:=0}\\<{" + 
//					"			while (i<a.length) {a[i] = a[i+1];" + 
//					"			i++;}" + 
//					"		}\\>true");
//		} catch (Exception e) {
//			// TODO Auto-generated catch block
//			System.out.println(e.getMessage());
//			if (e.getCause()!=null) {
//			System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//		CurrentLIG cur = new CurrentLIG(seq, services);
//		cur.getLow();
//		System.out.println(cur.low());
//	}
//	
//	public void testCase2() {
//		Term formula;
//				
//		try {
//			formula = parse("{i:=0}\\<{" + 
//					"			while (i<a.length) {a[i] = a[i+1];" + 
//					"			i++;}" + 
//					"		}\\>true");
//		} catch (Exception e) {
//			// TODO Auto-generated catch block
//			System.out.println(e.getMessage());
//			if (e.getCause()!=null) {
//			System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//		CurrentLIG cur = new CurrentLIG(seq, services);
//		cur.getIndexAndHigh();
//		System.out.println(cur.index());
//		System.out.println(cur.high());
//	}
//
//	public void testCase3() {
//		Term formula;
//				
//		try {
//			formula = parse("{i:=0}\\<{" + 
//					"			while (i<a.length) {a[i] = a[i+1];" + 
//					"			i++;}" + 
//					"		}\\>true");
//		} catch (Exception e) {
//			// TODO Auto-generated catch block
//			System.out.println(e.getMessage());
//			if (e.getCause()!=null) {
//			System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//		CurrentLIG cur = new CurrentLIG(seq, services);
//		cur.getIndexAndHigh();
//		System.out.println(cur.extractProgramVariable((Statement) UpdateApplication.getTarget(formula).javaBlock().program()));
//	}
//
//	public void testCase4() {
//		Term formula;
//				
//		try {
//			formula = parse("{i:=0}\\<{" + 
//					"			while (i<a.length) {a[i] = a[i+1];" + 
//					"			i++;}" + 
//					"		}\\>true");
//		} catch (Exception e) {
//			// TODO Auto-generated catch block
//			System.out.println(e.getMessage());
//			if (e.getCause()!=null) {
//			System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//		CurrentLIG cur = new CurrentLIG(seq, services);
//		cur.getLocSet();
//	}

	public void testCase5() {
		Term formulaLeft;
		Term formulaRight;

		try {
			formulaRight = parse("{i:=0}\\<{" + "			while (i<a.length) { a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formulaRight), false, true).sequent();
//		System.out.println("Seq1: " + seq.toString());
//		CurrentLIG cur = new CurrentLIG(services);
//		cur.mainAlg(seq);

		try {
			formulaLeft = parse("rPred({(a,arr(1+i))}, timestamp)," + "x = TRUE," + "wellFormed(heap)," + "i=0,"
					+ "timestamp= 1 + timestamp_0," + "x_1 = 0," + "a.length = x_2,"
					+ "\\if (0 < a.length) \\then (TRUE) \\else (FALSE) = x,"
					+ "x_arr = {x_arr:=x_arr_0}{x_arr:=a}x_arr," + "x_3 = {x_3:=x_3_0}{x_3:=i}x_3,"
					+ "x_arr_1 = {x_arr_1:=x_arr_1_0}{x_arr_1:=a}x_arr_1," + "x_5 = {x_5:=x_5_0}{x_5:=1 + i}x_5,"
					+ "x_4 = {x_4:=x_4_0}{x_4:=a[1+i]}x_4," + "heap = {heap:=heap_1}{heap:=heap[a[i] := a[1 +i]]}heap,"
					+ "x_6 = {x_6:=x_6_0}{x_6:=1 + i}x_6," + "i = {i:=i_2}{i:=1 + i}i");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		seq = seq.addFormula(new SequentFormula(formulaLeft), true, true).sequent();
//		System.out.println("Seq: " + seq.toString());
//		cur.mainAlg2(seq);
	}

//	public void testCase6() {
//		Term t = null;
//		try {
//			t = parse("i");
//		} catch (Exception e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		Term t1 = tb.add(t, tb.one());
//		Term t2 = tb.add(t, tb.one());
//		if (t1.equals(t2)) {
//			System.out.println("EQUAL");
//		}
//		else {
//			System.out.println(t1.toString());
//			System.out.println(t2.toString());
//		}

//}

	public void testCase7() {

		Term formula;

		try {
			formula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "a.length=10" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
//		System.out.println("Seq to find LI " + seq.toString());

		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	public void testCase8() {
		Term formulaRight;

		try {
			formulaRight = parse("{i:=3}\\<{" + "			while (i<a.length) {a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formulaRight), false, true).sequent();
//		System.out.println("Seq1: " + seq.toString());

		String[] arrLeft = { "rPred({(a,arr(1+i))}, timestamp)", "wPred({(a,arr(i))}, timestamp)", "i < a.length"
//				, "3<a.length"
//				, "wPred(arrayRange(a,Z(0(#)),sub(i,Z(1(#)))), timestamp-1)"
//				, "rPred(arrayRange(a,Z(1(#)),i), timestamp - 1)"
				, "rPred({(a,arr(i))}, timestamp-1)", "wPred({(a,arr(i-1))}, timestamp-1)"
//				
				, "rPred({(a,arr(i-1))}, timestamp-2)", "wPred({(a,arr(i-2))}, timestamp-2)"
//
				, "rPred({(a,arr(i-2))}, timestamp-3)", "wPred({(a,arr(i-3))}, timestamp-3)"

//				, "timestamp=6"
//				 "x = TRUE"
//				 ,"wellFormed(heap)"
				, "i=3"
//						, "i>0"
//				, "timestamp= 1 + timestamp_0"
//				, "x_1 = 0"
//						 ,"a.length = x_2"
//				, "\\if (0 < a.length) \\then (TRUE) \\else (FALSE) = x"
//				, "x_arr = {x_arr:=x_arr_0}{x_arr:=a}x_arr,"
//				+ "x_3 = {x_3:=x_3_0}{x_3:=i}x_3,"
//				+ "x_arr_1 = {x_arr_1:=x_arr_1_0}{x_arr_1:=a}x_arr_1,"
//				+ "x_5 = {x_5:=x_5_0}{x_5:=1 + i}x_5,"
//				+ "x_4 = {x_4:=x_4_0}{x_4:=a[1+i]}x_4,"
//				+ "heap = {heap:=heap_1}{heap:=heap[a[i] := a[1 +i]]}heap,"
//				+ "x_6 = {x_6:=x_6_0}{x_6:=1 + i}x_6,"
//				+ "i = {i:=i_2}{i:=1 + i}i"
		};
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
			System.out.println("Sequent: " + seq.toString());
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}

			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
//		cur.mainAlg2(seq);
	}

	public void testCase9_P() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = Object.arrayFct(a[i]); a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "a.length > 10" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	public void testCase9_N() {

		Term formula;

		try {
			formula = parse("{i:=1}\\<{" + "			while (i<=a.length-1) {a[i] = a[i-1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	public void testCase10() {

		Term formula;

		try {
			formula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = b[i];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	public void testCaseFor_mbps() {

		Term formula;

		try {
			formula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = 1;"
										 + "            	sum= sum + a[i];"
										 + "				i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	
	public void testCase11_Condition() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		//// a bit of a lengthy parsing
		
		try {
			
			formula = parse("{i:=0}\\<{while (i<=a.length-1) {"
//							+ "				a[i] = 1;"
							+ "				if(a[i]> 0){"
							+ "					a[i] = 1;"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = 0;"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
//							+ "        //@ merge_proc \"MergeByIfThenElse\";\n"
							+ "			i++;}"
							+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		
		MergePointInline inlineMergePoints = new MergePointInline(formula.sub(1).javaBlock().program(), false, services);
		ProgramElement s = inlineMergePoints.inline();
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
		
		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		//////////////////////////
		
		
		
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "cond!=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	public void testCase12() {

		Term formula;

		try {
			formula = parse("{i:=0 || j:=0}\\<{"
											+ "			while (i<=a.length-1 && j<=a.length-1) {a[i] = b[j];"
											+ "				i++;"
											+ "				j++;"
											+ "}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	
	public void testCase13() {

		Term formula;

		try {
			formula = parse("{i:=0 || j:=b.length}\\<{"
											+ "			while (i<=a.length-1 && j>=0) {a[i] = b[j];"
											+ "				i++;"
											+ "				j--;"
											+ "}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();

		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
		cur.mainAlg();
	}

	
	
	public static void main(String[] args) {
		TestPredicateConstruction tpc = new TestPredicateConstruction();
		long start = System.currentTimeMillis();
		tpc.testCase9_P();
		long end = System.currentTimeMillis();
		System.out.println(end - start);
	}

	
	
	public class MergePointInline extends CreatingASTVisitor { 
		
		public MergePointInline(ProgramElement root, boolean preservesPos, Services services) {
			super(root, preservesPos, services);
		}
		
		public ProgramElement inline()
	    {
	        stack.push(new ExtList());
	        walk(root());
	        ExtList el = stack.peek();
	        return el.get(ProgramElement.class);
	    }

	    protected void doAction(ProgramElement element)
	    {
	        if (element instanceof EmptyStatement) {
	        	LocationVariable newIndexVar = new LocationVariable(new ProgramElementName(tb.newName("#mpIndex", nss)), 
	        			services.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT));	            
	        	addChild(new MergePointStatement(newIndexVar));
	            changed();
	        }
	        else {
	            super.doAction(element);
	        }
	    }
	};
	
}
