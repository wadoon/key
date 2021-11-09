package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class SMTReplayer extends SMTProofExploiter {

    public Collection<NoPosTacletApp> getAllAssertionInsertTaclets() {
        return sf2InsertTaclet.values();
    }

    private final Map<SequentFormula, NoPosTacletApp> sf2InsertTaclet = new HashMap<>();

    private final Map<String, Map<Map<Term, NoPosTacletApp>, Node>>
        knownReplayedNodes = new HashMap<>();

    public void addKnownReplayedNode(String text, Node node,
                                     Map<Term, NoPosTacletApp> hypoTaclets) {
        // TODO: this seems to work, but is very slow!
        knownReplayedNodes.computeIfAbsent(text, e -> new HashMap<>()).put(hypoTaclets, node);
        //knownReplayedNodes.put(new Pair<>(text, new HashMap<>(hypoTaclets)), node);
    }

    public Node getKnownReplayedNode(String key,
                                     Map<Term, NoPosTacletApp> hypoTaclets) {
        // TODO: this seems to work, but is very slow!
        //return knownReplayedNodes.get(new Pair<>(key, hypoTaclets));

        Map<Map<Term, NoPosTacletApp>, Node> v1 = knownReplayedNodes.get(key);
        if (v1 != null) {
            return v1.get(hypoTaclets);
        }
        return null;
    }

    public SMTReplayer(SMTProblem problem) {
        super(problem);
        if (problem.getSolvers().size() != 1) {
            throw new IllegalStateException("Proof can only be replayed from single solver!");
        }
        if (problem.getFinalResult().isValid() != SMTSolverResult.ThreeValuedTruth.VALID) {
            throw new IllegalStateException("The SMT solver could not find a proof!");
        }
        if (problem.getSolvers().iterator().next().getType() != SolverType.Z3_NEW_TL_SOLVER) {
            throw new IllegalStateException("Only Z3 proofs using the new modular translation " +
                " can be replayed currently!");
        }
        SMTSolver solver = problem.getSolvers().iterator().next();
        smtOutput = solver.getSolverOutput();

        // make sure quantifier handling is enabled (otherwise automatic proof search, for example
        // for nnf-pos/-neg, will not be able to close some goals)
        // TODO: this could be set locally for only the relevant sub-goals
        // set to default Java strategy
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);

        // we wrap the original String keys in SMTExprInContext to be aware of the bound variables
        for (Map.Entry<String, Term> e : problem.getTranslationToTermMap().entrySet()) {
            // root: no bound variables
            addTranslationToTerm(e.getKey(), e.getValue());
        }
    }

    public void replay() {
        tree = parse(smtOutput);

        findProofStart();

        // collect bindings from let expressions in symbolTable
        BindingsCollector bindingsCollector = new BindingsCollector(this);
        tree.accept(bindingsCollector);

        // before starting the actual replay: disable OSS (otherwise some taclets will not be found)
        StrategyProperties newProps = proof.getSettings()
                                           .getStrategySettings()
                                           .getActiveStrategyProperties();
        newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        Strategy.updateStrategySettings(proof, newProps);

        // hide all original formulas (assertions), remember mapping to insert_hidden_... taclets
        for (SequentFormula sf : goal.sequent().antecedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
            TacletApp hide = ReplayTools.createTacletApp("hide_left", pio, goal);
            goal = ReplayTools.applyInteractive(goal, hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }
        for (SequentFormula sf : goal.sequent().succedent().asList()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            TacletApp hide = ReplayTools.createTacletApp("hide_right", pio, goal);
            goal = ReplayTools.applyInteractive(goal, hide).head();
            NoPosTacletApp insertRule = goal.node().getLocalIntroducedRules().iterator().next();
            sf2InsertTaclet.put(sf, insertRule);
        }

        // do actual replay (starting from found proof root)
        ReplayVisitor replayVisitor = new ReplayVisitor(this, goal);
        proofStart.accept(replayVisitor);
    }

    public NoPosTacletApp getInsertTacletForSF(SequentFormula sequentFormula) {
        return sf2InsertTaclet.get(sequentFormula);
    }
}
