package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.match.legacy.LegacyTacletMatcher;
import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by sarah on 4/5/17.
 *
 * @author Alexander Weigl
 */
public class ScriptApi {
    private final ProofApi api;
    private final EngineState state;

    public ScriptApi(ProofApi proofApi) {
        api = proofApi;
        state = new EngineState(api.getProof());
    }

    /**
     * Execute ScriptCommand onto goal node
     *
     * @param command to be applied with parameters set
     * @return List of new proof goals (possibly empty)
     * Should throw an Exception if command not applicable?
     */
    public <T> ScriptResults executeScriptCommand(
            ProofScriptCommandCall<T> call, ProjectedNode onNode,
            VariableAssignments varsAssignment) throws ScriptException, InterruptedException {
        //TODO VariableAssignments should be in instantiateCommand

        state.setGoal(onNode.getProofNode());
        call.command.execute((AbstractUserInterfaceControl) api.getEnv().getUi(),
                call.parameter, state);

        ImmutableList<Goal> goals = api.getProof()
                .getSubtreeGoals(onNode.getProofNode());
        //TODO filter for open goals if necessary
        ScriptResults sr = new ScriptResults();

        goals.forEach(g -> sr.add(ScriptResult.create(g.node(), onNode, call)));

        return sr;
    }

    /**
     * @param arguments
     * @param <T>
     * @return
     */
    public <T> ProofScriptCommandCall<T> instantiateCommand(
            ProofScriptCommand<T> command, Map<String, String> arguments)
            throws Exception {
        return new ProofScriptCommandCall<>(command,
                command.evaluateArguments(state, arguments));
    }

    //TODO
    public void applyRule(String ruleName, String posInOcc) {
        //TacletApp app = new PosTacletApp();
        //TODO over RuleCommand

    }

    /**
     * TODO: richtige Signatur noch zu tun, atm. erst einmal Testweise
     * U.a. is Rueckgabewert noch unklar, evtl. Liste mit instantiantions die leer sein kann bei misserfolg
     */
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
                api.getEnv().getServices(), api.getEnv().getServices().getNamespaces());
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
                api.getEnv().getServices(), api.getEnv().getServices().getNamespaces());
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
    }
    //matching Seq Term: matchResult
    //
    //toTerm(String, vars)

    //[(label, goal, vars)]
    //variablen klasse mit maps typen und werte linked hashmap
    //
    //chain of responsibility

    //getIntermediateTree (ScriptResults old, ScriptResults new) ~> Beweisbaum -> Shallow Copy
    //hier implementieren

    //isclosable
    //derivable : mache cut und dann auto, falls nicht schließt prune proof

}
