package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import edu.kit.iti.formal.psdbg.interpreter.MatcherApi;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.SortType;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.Signature;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import lombok.Getter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Interface to KeY Matcher Api
 *
 * @author S. Grebing
 */
public class KeYMatcher implements MatcherApi<KeyData> {
    private static final Logger LOGGER = LogManager.getLogger(KeYMatcher.class);
    private static final Name CUT_TACLET_NAME = new Name("cut");

    private List<MatchResult> resultsFromLabelMatch;

    @Getter
    private Services services;

    public KeYMatcher(Services services) {
        this.services = services;
    }

    /**
     * @param proof
     * @param kd
     * @param term
     * @return null if the term is not derivable or the new state
     */
    public static GoalNode<KeyData> isDerivable(Proof proof, GoalNode<KeyData> kd, Term term) {
        Taclet cut = proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = (SchemaVariable) app.uninstantiatedVars().iterator().next();
        TacletApp cutApp = app.addCheckedInstantiation(sv, term, proof.getServices(), true);
        ImmutableList<Goal> goalList = kd.getData().getGoal().apply(cutApp);

        if (goalList.size() != 2) {
            throw new IllegalStateException("Cut created more than two sub goals!");
        }

        // apply auto on the first (hope that is the "to show" case.
        Goal toShow = goalList.head();

        //apply auto to close this branch, from AutoCommand.java
        Profile profile = proof.getServices().getProfile();
        ApplyStrategy applyStrategy = new ApplyStrategy(profile.getSelectedGoalChooserBuilder().create());
        applyStrategy.start(proof, toShow);

        //check if there are no goals under toShow
        boolean isDerivable = proof.getSubtreeGoals(toShow.node()).size() == 0;

        if (isDerivable) {
            KeyData kdataNew = new KeyData(kd.getData(), goalList.head());
            GoalNode<KeyData> newGoalNode = new GoalNode<KeyData>(kd, kdataNew, kdataNew.isClosedNode());
            return newGoalNode;
        } else {
            proof.pruneProof(kd.getData().getNode(), false);
            return null;
        }
    }

    private static String cleanLabel(String label) {

        String cleaned = label.replaceAll(" ", "");
        cleaned = cleaned.replaceAll("\\(", "\\\\(");
        cleaned = cleaned.replaceAll("\\)", "\\\\)");
        cleaned = cleaned.replaceAll("\\[", "\\\\[");
        cleaned = cleaned.replaceAll("\\]", "\\\\]");

        return cleaned;
    }

    /**
     * If teh label matcher was successful the list contains all match results
     *
     * @return
     */
    public List<MatchResult> getResultsFromLabelMatch() {
        return resultsFromLabelMatch;
    }

    /**
     * Match the label of a goal node
     *
     * @param currentState goal node as possible match cancidate
     * @param label        String representation for regular expression for label to match
     * @return List of matches if match was sucessful, empty list otherwise
     */
    @Override
    public List<VariableAssignment> matchLabel(GoalNode<KeyData> currentState,
                                               String label) {
        List<VariableAssignment> assignments = new ArrayList<>();
        resultsFromLabelMatch = new ArrayList<>();
        //compile pattern
        String cleanLabel = cleanLabel(label);


        String branchLabel = currentState.getData().getBranchingLabel();
        String cleanBranchLabel = branchLabel.replaceAll(" ", "");
        //cleanLabel(branchLabel);


        Pattern regexpForLabel = Pattern.compile("\\\\Q" + cleanLabel + "\\\\E");
        Matcher branchLabelMatcher = regexpForLabel.matcher(Pattern.quote(cleanBranchLabel));

        //Matcher branchLabelMatcher = regexpForLabel.matcher(cleanBranchLabel);


        if (branchLabelMatcher.matches()) {
            VariableAssignment va = new VariableAssignment(null);
            va.declare("$$branchLabel_", SimpleType.STRING);
            va.assign("$$branchLabel_", Value.from(branchLabelMatcher.group()));
            assignments.add(va);
            resultsFromLabelMatch.add(branchLabelMatcher.toMatchResult());
        }

        String controlFlowLines = currentState.getData().getProgramLinesLabel();
        Matcher linesMatcher = regexpForLabel.matcher(controlFlowLines);
        if (linesMatcher.matches()) {
            VariableAssignment va = new VariableAssignment(null);
            va.declare("$$CtrlLinesLabel_", SimpleType.STRING);
            va.assign("$$CtrlLinesLabel_", Value.from(linesMatcher.group()));
            assignments.add(va);
            resultsFromLabelMatch.add(linesMatcher.toMatchResult());
        }

        String controlFlowStmts = currentState.getData().getProgramStatementsLabel();
        Matcher flowStmtsMatcher = regexpForLabel.matcher(controlFlowLines);
        if (flowStmtsMatcher.matches()) {
            VariableAssignment va = new VariableAssignment(null);
            va.declare("$$FlowStmtsLabel_", SimpleType.STRING);
            va.assign("$$FlowStmtsLabel_", Value.from(flowStmtsMatcher.group()));
            assignments.add(va);
            resultsFromLabelMatch.add(flowStmtsMatcher.toMatchResult());
        }

        String ruleLabel = currentState.getData().getRuleLabel();
        Matcher ruleMatcher = regexpForLabel.matcher(ruleLabel);
        if (ruleMatcher.matches()) {
            VariableAssignment va = new VariableAssignment(null);
            va.declare("$$RuleLabel_", SimpleType.STRING);
            va.assign("$$RuleLabel_", Value.from(ruleMatcher.group()));
            assignments.add(va);
            resultsFromLabelMatch.add(ruleMatcher.toMatchResult());
        }


        // assignments.forEach(variableAssignment -> System.out.println(variableAssignment));
        return assignments.isEmpty() ? null : assignments;
    }

    @Override
    public List<VariableAssignment> matchSeq(GoalNode<KeyData> currentState, String pattern) {
        KeyMatcherFacade kmf = new KeyMatcherFacade(currentState.getData().getEnv(), currentState.getData().getNode().sequent());
        //System.out.println("State that will be matched " + currentState.getData().getNode().sequent() + " with pattern " + pattern);
        //System.out.println("Signature " + sig.toString());
        Matchings m = kmf.matches(pattern);

        if (m.isNoMatch()) {
            LOGGER.debug("currentState has no match= " + currentState.getData().getNode().sequent());
            return Collections.emptyList();
        } else {
            Match firstMatch = m.getMatchings().iterator().next();
            VariableAssignment va = new VariableAssignment(null);
            for (String s : firstMatch.keySet()) {
                MatchPath matchPath = firstMatch.get(s);
                //if (!s.equals("EMPTY_MATCH")) {
                Term matched;
                try {
                    matched = (Term) matchPath.getUnit();
                    if (s.startsWith("?")) {

                        s = s.replaceFirst("\\?", "");
                    }

                    Value<String> value = toValueTerm(currentState.getData(), matched);
                    va.declare(s, value.getType());
                    va.assign(s, value);

                } catch (ClassCastException e) {
                    LogicVariable var = (LogicVariable) matchPath.getUnit();
                    String reprTerm = var.name().toString();
                    Value<String> value = new Value<>(
                            new TermType(new SortType(var.sort())),
                            reprTerm);
                    if (s.startsWith("?")) {
                        s = s.replaceFirst("\\?", "");
                    }
                    va.declare(s, value.getType());
                    va.assign(s, value);


                }
                //LOGGER.info("Variables to match " + s + " : " + value);
                //}
            }
            List<VariableAssignment> retList = new LinkedList();
            LOGGER.info("Matched Variables " + va.toString());
            retList.add(va);
            return retList;
        }
    }

    private Value<String> toValueTerm(KeyData currentState, Term matched) {

        String reprTerm = LogicPrinter.quickPrintTerm(matched, currentState.getProof().getServices());
        //Hack: to avoid newlines
        String reprTermReformatted = reprTerm.trim();
        return new Value<>(
                new TermType(new SortType(matched.sort())),
                reprTermReformatted
        );
    }

    //private TermLiteral from(SequentFormula sf) {
    //    return new TermLiteral(sf.toString());
    //}
}
