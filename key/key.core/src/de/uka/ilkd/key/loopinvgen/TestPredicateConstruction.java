package de.uka.ilkd.key.loopinvgen;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URL;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.util.KeYResourceManager;

public class TestPredicateConstruction {

	private final TermFactory tf;
	private final TermBuilder tb;
	private final NamespaceSet nss;
	private final Services services;

//	private String pathToTestKeYFile = "C:\\Users\\Asma\\git\\LIG_3\\key\\key\\key.core\\src\\de\\uka\\ilkd\\key\\loopinvgen\\test.key";

	TestPredicateConstruction() {
		URL urlToTestFile = KeYResourceManager.getManager().getResourceFile(this, "test.key");
		services = HelperClassParsingTests.createServices(new File(urlToTestFile.getFile()));
		tb = services.getTermBuilder();
		nss = services.getNamespaces();
		tf = tb.tf();
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

	public void shiftArrayToLeft() {////////////////////DONE!

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "		while (i<a.length-1) {a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
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
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGNew curNew = new LIGNew(services, seq);
		curNew.mainAlg();
	}

	public void shiftArrayToLeftWithBreak() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {"
					+ "if (i==a.length-1) break;"
					+ "else {a[i] = a[i+1];"
					+ "			i++;}}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
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
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGNew curNew = new LIGNew(services, seq);
		curNew.mainAlg();
	}

	
	public void withFunc() {////////////////////DONE!

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = Object.arrayFct(a[i]);" + "			i++;}"
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

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
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
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGNew cur = new LIGNew(services, seq);
		cur.mainAlg();
	}

	public void withoutFunc() {////////////////////DONE!

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = a[i];" + "			i++;}"
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

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
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
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}

		LIGNew cur = new LIGNew(services, seq);
		cur.mainAlg();
	}

	public void stencil() {

		Term succFormula;

		try {
			succFormula = parse("{i:=1}\\<{" + "			while (i<a.length-1) {a[i] = a[i-1] + a[i+1];" + "			i++;}"
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

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
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
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}
		
		LIGNew curNew = new LIGNew(services, seq);
		curNew.mainAlg();
	}
//
//	public void shiftArrayToLeftWithAiliasing() {
//		Term succFormula;
//		try {
//			succFormula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = b[i+1];" + "			i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();
//
//		String[] arrLeft = { "noW(arrayRange(a,0,a.length))","noR(arrayRange(a,0,a.length))", "a.length > 10" };
//		String[] arrRight = { "a=null", "b=null", "a!=b", "a.length!=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		
//		try {
//			for (String fml : arrRight) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		
//		LIGNew curNew = new LIGNew(services, seq);
//		curNew.mainAlg();
//	}
//	
//	public void shiftArrayToLeftWithoutAiliasing() { //Done
//		Term succFormula;
//
//		try {
//			succFormula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = b[i+1];" + "			i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();
//
//		String[] arrLeft = {"a!=null", "a.length > 10", "a!=b", "b!=null", "a.length=b.length"};
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
//		cur.mainAlg();
//	}
//
//	
	public void condition() {//////////////DONE!
		Term formula;
		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		//// a bit of a lengthy parsing
		try {
			
			formula = parse("{i:=0}\\<{while (i<=a.length-1) {"
							+ "				if(i > (a.length-1)/2){"
							+ "					a[i] = 1;"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = 0;"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElse\";\n"
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
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = {"noR(arrayRange(a,0,a.length))", "noW(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrRight = {"a=null"};
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
		LIGNew cur = new LIGNew(services, seq);
		cur.mainAlg();
	}

	public void conditionDifferentNumberOfEvents() {/////////////DONE!

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=0}\\<{while (i<a.length-1) {"
							+ "				if(i> (a.length-1)/2){"
							+ "					a[i] = a[i+1];"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = 1;"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElseAntecedent\";\n"
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
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
		
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = { "noW(arrayRange(a,0,a.length))","noR(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrRight = {"a=null" };
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
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}


		LIGNew curNew = new LIGNew(services, seq);
		curNew.mainAlg();
	
	}
	public void conditionWithDifferentEvents() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=1}\\<{while (i<a.length-1) {"
							+ "				if(i> (a.length-1)/2){"
							+ "					a[i] = a[i+1];"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = a[i-1];"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElseAntecedent\";\n"
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
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
		
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length>10" };
		String[] arrRight = {"a=null" };
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
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return;
		}


		LIGNew curNew = new LIGNew(services, seq);
		curNew.mainAlg();
	
	}

	
//
//	
//	
//	
//
//	public void testCaseFor_mbps() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = 1;"
//										 + "            	sum= sum + a[i];"
//										 + "				i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
//		cur.mainAlg();
//	}
//
//	
//	
//	public void testCase12() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0 || j:=0}\\<{"
//											+ "			while (i<=a.length-1 && j<=a.length-1) {a[i] = b[j];"
//											+ "				i++;"
//											+ "				j++;"
//											+ "}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
//		cur.mainAlg();
//	}
//
//	
//	public void testCase13() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0 || j:=b.length}\\<{"
//											+ "			while (i<=a.length-1 && j>=0) {a[i] = b[j];"
//											+ "				i++;"
//											+ "				j--;"
//											+ "}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
////		LIGMultipleArrays cur = new LIGMultipleArrays(services, seq);
////		cur.mainAlg();
//	}

	
	public static void main(String[] args) {
		TestPredicateConstruction tpc = new TestPredicateConstruction();
		long start = System.currentTimeMillis();
//		tpc.shiftArrayToLeft();
//		tpc.shiftArrayToLeftWithBreak();
//		tpc.condition();
//		tpc.conditionDifferentNumberOfEvents();
//		tpc.conditionWithDifferentEvents();
//		tpc.withFunc();
//		tpc.withoutFunc();
		tpc.stencil(); //Change the s0 in LIGNew
		long end = System.currentTimeMillis();
		System.out.println("Loop Invariant Generation took " + (end - start) + " ms");
	}
}