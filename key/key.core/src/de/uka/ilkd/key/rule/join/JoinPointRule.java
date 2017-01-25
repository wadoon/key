package de.uka.ilkd.key.rule.join;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.DisjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.SimplePredicateAbstractionLattice;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ContainsStatementVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

public class JoinPointRule implements BuiltInRule {
    public static final JoinPointRule INSTANCE = new JoinPointRule();

    private static final String DISPLAY_NAME = "Join Point";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public JoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        PosInOccurrence pio = ruleApp.posInOccurrence();
        JoinRuleBuiltInRuleApp app = new JoinRuleBuiltInRuleApp(new JoinRule(),
                pio);

        StatementBlock block = (StatementBlock) JoinRuleUtils
                .getJavaBlockRecursive(pio.subTerm()).program();

        JoinPointStatement jPS = ((JoinPointStatement) block
                .getInnerMostMethodFrame().getBody().getFirstElement());

        String[] params = jPS.getJoinParams();

        JoinProcedure concreteRule = jPS.getJoinProc();

        if (concreteRule.toString().equals("JoinByPredicateAbstraction")) {
            Class<? extends AbstractPredicateAbstractionLattice> latticeType = translateLatticeType(
                    params[0]);
            List<AbstractionPredicate> predicates = hasCorrectParams(params[1],
                    goal);
            final JoinWithPredicateAbstractionFactory absPredicateFactory = (JoinWithPredicateAbstractionFactory) concreteRule;
            concreteRule = absPredicateFactory.instantiate(predicates,
                    latticeType,
                    new LinkedHashMap<ProgramVariable, AbstractDomainElement>());
        }

        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                .findPotentialJoinPartners(goal, pio, goal.proof().root());

        app.setJoinNode(goal.node());
        app.setConcreteRule(concreteRule);
        app.setJoinPartners(joinPartners);

        ImmutableList<Goal> newGoals = goal.split(1);
        Goal g = newGoals.head();
        newGoals = g.apply(app);

        return newGoals;
    }

    private Class<? extends AbstractPredicateAbstractionLattice> translateLatticeType(
            String type) {
        if (type.equals("simple"))
            return SimplePredicateAbstractionLattice.class;
        else if (type.equals("conjunctive"))
            return ConjunctivePredicateAbstractionLattice.class;
        else if (type.equals("disjunctive"))
            return DisjunctivePredicateAbstractionLattice.class;
        else return null;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && !goal.isLinked()
                && JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(pio.subTerm())
                                .javaBlock()) instanceof JoinPointStatement) {

            JoinPointStatement jps = ((JoinPointStatement) JavaTools
                    .getActiveStatement(TermBuilder
                            .goBelowUpdates(pio.subTerm()).javaBlock()));

            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);

            if (!joinPartners.isEmpty() && (!jps.getJoinProc().toString()
                    .equals("JoinByPredicateAbstraction")
                    || !hasCorrectParams(jps.getJoinParams()[1], goal)
                            .isEmpty())) {

                ImmutableList<Goal> joinPartnersGoal = ImmutableSLList.nil();

                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                    joinPartnersGoal = joinPartnersGoal.append(p.first);
                }

                ImmutableList<Goal> openGoals = goal.node().proof().openGoals();
                for (Goal g : openGoals) {
                    if (!g.equals(goal) && !g.isLinked()
                            && !joinPartnersGoal.contains(g)
                            && containsNonActiveJPS(g, jps)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

    private List<AbstractionPredicate> hasCorrectParams(String params, Goal g) {

        List<AbstractionPredicate> result = new ArrayList<AbstractionPredicate>();
        Services services = g.proof().getServices();
        try {
            Pattern p = Pattern.compile("\\\\(.+?) -> \\{(.+?)\\}");
            Matcher m = p.matcher(params);
            while (m.find()) {
                for (int i = 1; i < m.groupCount(); i += 2) {

                    final String phStr = m.group(i);
                    final String[] predStr = m.group(i + 1).split(", ");

                    // Parse the placeholder
                    Pair<Sort, Name> ph = null;
                    ph = JoinRuleUtils.parsePlaceholder(phStr, false,
                            g.proof().getServices());
                    if (services.getNamespaces().variables()
                            .lookup(ph.second) == null) {
                        services.getNamespaces().variables()
                                .add(new LocationVariable(
                                        new ProgramElementName(
                                                ph.second.toString()),
                                        ph.first));
                    }

                    ArrayList<Pair<Sort, Name>> phList = JoinRuleUtils
                            .singletonArrayList(ph);

                    for (int j = 0; j < predStr.length; j++) {
                        result.add(JoinRuleUtils.parsePredicate(predStr[j],
                                phList, services));
                    }

                }

            }

        } catch (ParserException | JoinRuleUtils.SortNotKnownException e) {
            result = new ArrayList<AbstractionPredicate>();
            e.printStackTrace();
        }
        return result;
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @return
     */
    static boolean containsNonActiveJPS(Goal g, JoinPointStatement jps) {
        return containsJPS(g, jps, true);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @return
     */
    static boolean containsJPS(Goal g, JoinPointStatement jps) {
        return containsJPS(g, jps, false);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @param onlyNonActive
     * @return
     */
    private static boolean containsJPS(Goal g, JoinPointStatement jps,
            boolean onlyNonActive) {
        for (SequentFormula sf : g.node().sequent().succedent()) {
            JavaBlock jb = JoinRuleUtils.getJavaBlockRecursive(sf.formula());

            if (jb.isEmpty()) {
                continue;
            }

            if (onlyNonActive && JavaTools.getActiveStatement(jb).equals(jps)) {
                return false;
            }

            Services services = g.proof().getServices();
            MethodFrame mf = JavaTools.getInnermostMethodFrame(jb, services);

            if (mf != null) {
                ContainsStatementVisitor visitor = new ContainsStatementVisitor(
                        mf, jps, services);
                visitor.start();
                return visitor.isContained();
            } else {
                return false;
            }
        }

        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new JoinPointBuiltInRuleApp(this, pos);
    }

}
