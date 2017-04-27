package de.uka.ilkd.key.prototype;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.match.legacy.LegacyTacletMatcher;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.Iterator;

/**
 * @author Alexander Weigl
 * @version 1 (18.04.17)
 */
public class SequentViewer extends Application {
    private Services services;
    private NamespaceSet nss;

    @Override public void start(Stage stage) throws Exception {
        Sequent s = createTestSequent();

        Pane viewer = new SequentPane(s, services);
        Scene scene = new Scene(viewer, 500d, 800d);
        scene.getStylesheets().add("/style.css");
        stage.setScene(scene);
        stage.show();
    }

    public static final void main(String[] args) {
        new SequentViewer().launch(args);
    }

    private Sequent createTestSequent()
            throws ProblemLoaderException, ParserException {
        KeYEnvironment<?> env = KeYEnvironment.load(new File(
                "key.ui/src/de/uka/ilkd/key/prototype/test.key"));

        DefaultTermParser dtp = new DefaultTermParser();
        StringReader r = new StringReader(// "a=5 ==> \\<{int i = 0;}\\>(a=5)");
                //   "(5 = a) & (15 = add(b, -3)) ==> (mul(a, b) = 90)");
                " fi(c) ==> p(d), fi(c)");
        nss = env.getServices().getNamespaces();

        AbbrevMap abbrev = new AbbrevMap();

        Sequent seq = dtp.parseSeq(r, env.getServices(), nss, abbrev);

        services = env.getServices();


        parseDecls("\\sorts { s; }\n" +
                "\\functions {\n" +
                "  s f(s);\n" +
                "}\n" +
                //  "\\predicates {\n"+ "fi(s);\n"+ "}\n"+
                "\\schemaVariables {\n" +
                "  \\formula b,b0,post;\n" +
                "  \\program Statement #p1, #s ; \n" +
                "  \\program Expression #e2, #e ; \n" +
                "  \\program SimpleExpression #se ; \n" +
                "  \\program Variable #slhs, #arr, #ar, #ar1 ; \n" +
                "  \\program LoopInit #i ; \n" +
                "  \\program Label #lab, #lb0, #lb1 ; \n" +
                "  \\program Label #inner, #outer ; \n" +
                "  \\program Type #typ ; \n" +
                "  \\program Variable #v0, #v, #v1, #k, #boolv ; \n" +
                "  \\program[list] Catch #cf ; \n" +
                "  \\term s x,x0,x1 ;\n" +
                "  \\skolemTerm s sk ;\n" +
                "  \\variables s z,z0 ;\n" +
                "}\n"
        );

        String imprightString =
                "test{\\assumes( fi(x) ==> fi(x)) \\find (==>)  \\add (==>)}";
        //"test{\\assumes (==> b -> b0 ) \\find (b) \\add (==> b -> b0)}";
        // "imp_right{\\find(==> x = x0) \\assumes (==> x1 = x0) \\add(==> x0 = x)}";

        //Term te = parseTerm("p(x) ==> p(x)");
        //TacletMatchProgram.createProgram(te);

        Taclet t = parseTaclet(imprightString);

        LegacyTacletMatcher ltm = new LegacyTacletMatcher(t);

        //do we need taclet choice model?
       /* ltm.matchIf(( i < asize ?
                      antecCand : succCand ), ifFma, matchCond, services).getFormulas ()
*/

        //===============================
        MatchConditions mc = MatchConditions.EMPTY_MATCHCONDITIONS;
        Sequent ifseq = t.ifSequent();
        int asize = ifseq.antecedent().size();
        int size = asize + ifseq.succedent().size();
        System.out.println("Assumes Clause: " +ifseq);


        if (size > 0) {
            ImmutableList<IfFormulaInstantiation> antecCand =
                    IfFormulaInstSeq.createList(seq, true);
            ImmutableList<IfFormulaInstantiation> succCand =
                    IfFormulaInstSeq.createList(seq, false);

            Iterator<SequentFormula> pattern = ifseq.iterator();
//           // while(it.hasNext()) {
//            MatchConditions mat = ltm.matchIf(antecCand, mc, services);
//            System.out.println("Inst after antec: "+mc.getInstantiations());
//            System.out.println(mat.getInstantiations());
//            MatchConditions mb = ltm.matchIf(succCand, mat, services);
//            System.out.println("Inst after succ: "+mc.getInstantiations());
//            System.out.println(mb.getInstantiations());
//            //}

            MatchConditions matchCond = MatchConditions.EMPTY_MATCHCONDITIONS;

            //TacletAssumesModel[] ifChoiceModel = new TacletAssumesModel[size];

            for (int i = 0; i < size; i++) {
                final Term patternTerm = pattern.next().formula();
                System.out.println(patternTerm);
//                ifChoiceModel[i] =
//                        new TacletAssumesModel(ifFma,
//                                ltm.matchIf((i < asize ?
//                                        antecCand : succCand), ifFma, matchCond, services).getFormulas(),
//                                services, nss, abbrev);

                boolean inAntecedent = i < asize;
                IfMatchResult ma = ltm.matchIf((inAntecedent ?
                        antecCand : succCand), patternTerm, matchCond, services);

                ImmutableList<MatchConditions> testma = ma.getMatchConditions();

                matchCond = ma.getMatchConditions().head();
                /*
                for (MatchConditions matchConditions : testma) {
                    System.out.println(  matchConditions.getInstantiations());
                }*/

            }
        } else{
            TacletAssumesModel[] ifChoiceModel = new TacletAssumesModel [ 0 ];

        }



        //==========================
/*
        ImmutableList<IfFormulaInstantiation> listAnte = IfFormulaInstSeq.createList(seq, true);
        ImmutableList<IfFormulaInstantiation> listSucc = IfFormulaInstSeq.createList(seq, false);
        //ltm.matchIf();
        MatchConditions x = ltm.matchIf(listAnte, mc, services);
        System.out.println(x);


        //hier wird null zurückgegeben, weil die letzte Formel nicht matcht,
        //problem, dass die Position doch keine Rolle spielt
        MatchConditions x1 = ltm.matchIf(listSucc, x, services);
        System.out.println(x.getInstantiations());
        System.out.println(x1);
    //    System.out.println(x1.getInstantiations());

        //Aufteilen: antec+succ hintereinander: Frage welche Match-Methode
        // matchfind: find darf nicht mehrere top level formeln enthalten

      //  final TacletMatcher matcher = t.getMatcher();

        // IfMatchResult imr = t.getMatcher().matchIf()
       // IfMatchResult mr = t.getMatcher().matchIf(p_toMatch, p_ifSeqTail.head().formula(), p_matchCond, p_services);

       // System.out.println(matcher);

       // TacletMatchProgram.createProgram(
                //"p(x) ==> p(x)")

     //   MatchConditions ma = t.getMatcher().matchFind(s.succedent().get(0).formula(), mc, services);
        //System.out.println(mc);
     //   System.out.println(ma);
        //System.out.println(matchConditions);
      //  System.out.println(s.succedent().get(0).formula());
      */
        return seq;

    }

/*    private void initIfChoiceModels() {
 	Sequent ifseq   = taclet().ifSequent();
	int     asize   = ifseq.antecedent().size();
	int     size    = asize + ifseq.succedent().size();

	if ( size > 0 ) {
	    ImmutableList<IfFormulaInstantiation> antecCand =
		IfFormulaInstSeq.createList ( seq, true );
	    ImmutableList<IfFormulaInstantiation> succCand  =
		IfFormulaInstSeq.createList ( seq, false );

	    Iterator<SequentFormula> it        = ifseq.iterator();
	    Term                         ifFma;
	    MatchConditions              matchCond = app.matchConditions ();

	    ifChoiceModel                          = new TacletAssumesModel[size];

	    for (int i=0; i<size; i++) {
		ifFma            = it.next ().formula ();
		ifChoiceModel[i] =
		    new TacletAssumesModel ( ifFma,
					taclet ().getMatcher().matchIf(( i < asize ?
                      antecCand : succCand ), ifFma, matchCond, services).getFormulas (),
					services, nss, scm);
	    }
	} else
	    ifChoiceModel = EMPTY_IF_CHOICES;
    }*/


    private KeYParserF stringDeclParser(String s) {
        return new KeYParserF(ParserMode.DECLARATION,
                new KeYLexerF(s,
                        "No file. parser/TestTacletParser.stringDeclParser(" + s + ")"),
                services, nss);
    }

    public void parseDecls(String s) {
        try {
            KeYParserF p = stringDeclParser(s);
            p.decls();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw );
        }
    }



    private KeYParserF stringTacletParser(String s) {
        return new KeYParserF(ParserMode.TACLET, new KeYLexerF(s,
                "No file. CreateTacletForTests.stringTacletParser(" + s + ")"),
                services,
                nss);
    }

    Taclet parseTaclet(String s) {
        try {
            KeYParserF p = stringTacletParser(s);

            return p.taclet(DefaultImmutableSet.<Choice>nil());
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw );
        }
    }
    Term parseTerm(String s) {
        try {
            KeYParserF p = new KeYParserF(ParserMode.TERM, new KeYLexerF(s,
                "No file. CreateTacletForTests.stringTacletParser(" + s + ")"),
                services,
                nss);

            return p.termEOF();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw );
        }
    }

    /*private Sequent createTestSequent()
            throws ProblemLoaderException, ParserException {
        KeYEnvironment ke = KeYEnvironment.load(new File(
                "key.ui/examples/standard_key/pred_log/clam-examples/004.key"));

        DefaultTermParser dtp = new DefaultTermParser();
        StringReader r = new StringReader("\\forall int x; \\forall int j; j <= ms(x)*j\n"
                + "->\n" + "\t\\forall int a; \\forall int b; \\forall int c;\n"
                + "\t(ms(c) + ms(a)*ms(a) + ms(b)*ms(b) <\n"
                + "\t ms(c) + ms(b)*ms(b) + 2*ms(a)*ms(a)*ms(b) + ms(a)*ms(a)*ms(a)*ms(a))");
        NamespaceSet nss = new NamespaceSet();
        AbbrevMap abbrev = new AbbrevMap();
        return dtp.parseSeq(r,ke.getServices(),nss, abbrev);
    }*/
}
