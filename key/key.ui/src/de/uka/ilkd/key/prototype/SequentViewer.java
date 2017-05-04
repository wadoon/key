package de.uka.ilkd.key.prototype;

import de.uka.ilkd.key.api.VariableAssignments;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

import java.io.File;
import java.io.StringReader;

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

    public static void main(String[] args) {
        new SequentViewer().launch(args);
    }

    private Sequent createTestSequent()
            throws ProblemLoaderException, ParserException {
        KeYEnvironment<?> env = KeYEnvironment.load(new File(
                "key.ui/src/de/uka/ilkd/key/prototype/test.key"));

        DefaultTermParser dtp = new DefaultTermParser();
        StringReader r = new StringReader(// "a=5 ==> \\<{int i = 0;}\\>(a=5)");
                //   "(5 = a) & (15 = add(b, -3)) ==> (mul(a, b) = 90)");
                // " fi(c), fi(d) ==> fi(d), fi(c)");
                " c = d , d= c, fi(d) ==> fi(c), fi(d)");
        nss = env.getServices().getNamespaces();

        AbbrevMap abbrev = new AbbrevMap();

        Sequent seq = dtp.parseSeq(r, env.getServices(), nss, abbrev);

        services = env.getServices();

        VariableAssignments testAssign = new VariableAssignments(null);
        try {
            testAssign.addType("x0", VariableAssignments.VarType.INT);
            testAssign.addType("x1", VariableAssignments.VarType.INT);
            testAssign.addType("x", VariableAssignments.VarType.INT);
        } catch (Exception e) {
            e.printStackTrace();
        }

        String testPattern = "x0=x, x1=x==> fi(x0)";
        //matchPattern(testPattern, seq, testAssign, services);


        return seq;
    }
/*
    /**
     * TODO: richtige Signatur noch zu tun, atm. erst einmal Testweise
     * Es muessten noch die Assignments mit gegebene werden mit Typeninfo

    public void matchPattern(String pattern, Sequent currentSeq, VariableAssignments assignments, Services services){
        //Aufbau der Deklarationen für den NameSpace
        buildNameSpace(services, assignments);
        //Zusammenbau des Pseudotaclets
        //Parsen des Taclets
        String patternString = "matchPattern{\\assumes("+pattern+") \\find (==>)  \\add (==>)}";

        Taclet t = null;
        try {
            t = parseTaclet(patternString);
        } catch (RecognitionException e) {
            e.printStackTrace();
        }

        //Build Matcher for Matchpattern
        LegacyTacletMatcher ltm = new LegacyTacletMatcher(t);

        NamespaceSet nss = services.getNamespaces();

        //patternSequent
        Sequent patternSeq = t.ifSequent();
        int asize = patternSeq.antecedent().size();
        int size = asize + patternSeq.succedent().size();
        //Iterator durch die Pattern-Sequent
        if(size > 0) {
            Iterator<SequentFormula> patternIterator = patternSeq.iterator();

            //Init mit leeren Matchconditions, die gefüllt werden
            MatchConditions matchCond = MatchConditions.EMPTY_MATCHCONDITIONS;

            //Iteratoren durch die Sequent
            ImmutableList<IfFormulaInstantiation> antecCand =
                    IfFormulaInstSeq.createList(currentSeq, true);
            ImmutableList<IfFormulaInstantiation> succCand =
                    IfFormulaInstSeq.createList(currentSeq, false);

            SequentFormula[] patternArray = new SequentFormula[patternSeq.size()];
            {
                int i = 0;
                for (SequentFormula fm : patternSeq)
                    patternArray[i++] = fm;
            }


            Queue<SearchNode> queue = new LinkedList<>();
            //init
            queue.add(new SearchNode(patternArray, asize, antecCand, succCand));
            List<SearchNode> finalCandidates = new ArrayList<>(100);

            while (!queue.isEmpty()) {
                SearchNode node = queue.remove();
                boolean inAntecedent = node.isAntecedent();
                System.out.println(inAntecedent ? "In Antec: " : "In Succ");

                IfMatchResult ma = ltm.matchIf((inAntecedent ?
                        antecCand : succCand), node.getPatternTerm(), node.mc, services);

                if (!ma.getMatchConditions().isEmpty()) {
                    ImmutableList<MatchConditions> testma = ma.getMatchConditions();

                    Iterator<MatchConditions> iter = testma.iterator();
                    while (iter.hasNext()) {
                        SearchNode sn = new SearchNode(node, iter.next());

                        if (sn.isFinished()) {
                            finalCandidates.add(sn);
                        } else {
                            queue.add(sn);
                        }
                    }


                } else {
                    System.out.println("Pattern Empty");
                }
            }
            for (SearchNode finalCandidate : finalCandidates) {
                System.out.println(finalCandidate.mc.getInstantiations());
            }
        }
    }

    private void buildNameSpace(Services services, VariableAssignments assignments) {
        String decalarations = buildDecls(assignments);
        parseDecls(decalarations);

    }

    private String buildDecls(VariableAssignments assignments) {
        Map<String, VariableAssignments.VarType> typeMap = assignments.getTypeMap();
        String schemaVars =  "\\schemaVariables {\n" ;
        final List<String> strn = new ArrayList<>();

        typeMap.forEach((id, type) -> strn.add(toDecl(id,type)));
        schemaVars += strn.stream().collect(Collectors.joining("\n"));
        schemaVars +="}";
        System.out.println(schemaVars);
        return schemaVars;
    }

    private String toDecl(String id, VariableAssignments.VarType type){
        String s ="";
        switch (type) {
            case ANY:
                s += "\\term any "+id+";";
                break;
            case BOOL:
                s += "\\term boolean "+id+";";
                break;
            case INT:
                s+= "\\term int "+id+";";
                break;
            case FORMULA:
                s+= "\\formula "+id+";";
                break;
            case INT_ARRAY:
                s+= "\\term int[] "+id+";";
                break;
            default:
                System.out.println("Sort "+type+" not supported yet");
                break;
        }
        return s;
    }

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

    Taclet parseTaclet(String s) throws RecognitionException {
        try {
            KeYParserF p = stringTacletParser(s);

            return p.taclet(DefaultImmutableSet.<Choice>nil());
        } catch (RecognitionException e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw e;
        }
    }*/
    /*Term parseTerm(String s) throws RecognitionException {
        try {
            KeYParserF p = new KeYParserF(ParserMode.TERM, new KeYLexerF(s,
                "No file. CreateTacletForTests.stringTacletParser(" + s + ")"),
                services,
                nss);

            return p.termEOF();
        } catch (RecognitionException e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw e;
        }
    }*/

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
