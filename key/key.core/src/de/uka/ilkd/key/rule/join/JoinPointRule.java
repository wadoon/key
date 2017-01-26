package de.uka.ilkd.key.rule.join;

import java.util.LinkedHashMap;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.SimpleBlockContract;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
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

        String params = jPS.getContract().getJoinParams();

        JoinProcedure concreteRule = jPS.getJoinProc();

        if (concreteRule.toString().equals("JoinByPredicateAbstraction")) {
            concreteRule = getProcedure(params, concreteRule, services);
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

    private JoinWithPredicateAbstraction getProcedure(String params, JoinProcedure joinProc, Services services) {
        Class<? extends AbstractPredicateAbstractionLattice> latticeType = null;
        List<AbstractionPredicate> predicates = null;
        Pattern p = Pattern.compile("\\\\(.+?)\\( ([^\\\\]+)\\)");
        Matcher m = p.matcher(params);
        while (m.find()) {
            if (m.group(1).equals("rep")) {
                
                URL path = JMLSpecFactory.class.getResource("domains.txt");
                String line = "";
                File f = new File(path.getFile());
                boolean found = false;
                try (BufferedReader br = new BufferedReader(
                        new FileReader(f))) {
                    while ((line = br.readLine()) != null && !found) {
                        String[] content = line.split(",", 3);
                        if (m.group(2).equals(content[0])) {
                            found = true;
                            latticeType =  translateLatticeType(content[1]);
                            predicates = getPredicates(content[2], services);
                        }
                    }
                }
                catch (IOException e) {

                }

            }
            else {
                latticeType = translateLatticeType(m.group(1));
                predicates = getPredicates(m.group(2), services);
            }
        }
        final JoinWithPredicateAbstractionFactory absPredicateFactory = (JoinWithPredicateAbstractionFactory) joinProc;
         return absPredicateFactory.instantiate(predicates, latticeType,
                new LinkedHashMap<ProgramVariable, AbstractDomainElement>());
    }

    private Class<? extends AbstractPredicateAbstractionLattice> translateLatticeType(
            String type) {
        if (type.equals("simple"))
            return SimplePredicateAbstractionLattice.class;
        else if (type.equals("conjunctive"))
            return ConjunctivePredicateAbstractionLattice.class;
        else if (type.equals("disjunctive"))
            return DisjunctivePredicateAbstractionLattice.class;
        else
            return null;
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

            BlockContract contract = ((JoinPointStatement) JavaTools
                    .getActiveStatement(TermBuilder
                            .goBelowUpdates(pio.subTerm()).javaBlock()))
                                    .getContract();

            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);

            if (!joinPartners.isEmpty() && (!contract.getJoinProcedure()
                    .toString().equals("JoinByPredicateAbstraction")
                    || !hasCorrectParams(contract.getJoinParams(),
                            goal.proof().getServices()))) {

                ImmutableList<Goal> joinPartnersGoal = ImmutableSLList.nil();

                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                    joinPartnersGoal = joinPartnersGoal.append(p.first);
                }

                ImmutableList<Goal> openGoals = goal.node().proof().openGoals();
                for (Goal g : openGoals) {
                    if (!g.equals(goal) && !g.isLinked()
                            && !joinPartnersGoal.contains(g)
                            && (hasSameBlockContractRule(g, contract)
                                    || hasSameBlock(g, contract.getBlock()))) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

    private boolean hasCorrectParams(String params, Services services) {
        Pattern p = Pattern.compile("\\\\(.+?)\\( ([^\\\\]+)\\)");
        Matcher m = p.matcher(params);
        boolean matched = false;

        while (m.find()) {
            matched = true;
            if (m.groupCount() != 2)
                return false;
            else {
                List<AbstractionPredicate> predicates = getPredicates(
                        m.group(2), services);
                if (((m.group(1).equals("conjunctive")
                        || m.group(1).equals("disjunctive")
                        || m.group(1).equals("simple")) && predicates.isEmpty())
                        || !m.group(1).equals("rep"))
                    return false;
            }
        }
        return matched;
    }

    private List<AbstractionPredicate> getPredicates(String predicatesStr,
            Services services) {
        List<AbstractionPredicate> result = new ArrayList<AbstractionPredicate>();
        Pattern p = Pattern.compile("(.+?) -> \\{(.+?)\\}");
        Matcher m = p.matcher(predicatesStr);
        while (m.find()) {
            if (m.groupCount() != 2) {
                result.clear();
                break;
            }
            else {
                try {
                    final String phStr = m.group(1);
                    final String[] predStr = m.group(2).split(", ");
                    Pair<Sort, Name> ph = null;
                    ph = JoinRuleUtils.parsePlaceholder(phStr, false, services);
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
                catch (ParserException
                        | JoinRuleUtils.SortNotKnownException e) {
                    result.clear();
                }

            }
        }

        return result;
    }

    private boolean hasSameBlockContractRule(Goal g, BlockContract contract) {
        for (RuleApp rA : g.appliedRuleApps()) {
            if (rA instanceof BlockContractBuiltInRuleApp
                    && ((BlockContractBuiltInRuleApp) rA).getContract()
                            .equals(contract))
                return true;
        }
        return false;
    }

    private boolean hasSameBlock(Goal g, StatementBlock block) {
        for (int i = 0; i < g.node().sequent().succedent().size(); i++) {
            JavaBlock jB = JoinRuleUtils.getJavaBlockRecursive(
                    g.node().sequent().succedent().get(i).formula());
            MethodFrame mF = JavaTools.getInnermostMethodFrame(jB,
                    g.proof().getServices());
            if (mF != null && hasSameBlockHelp(mF.getBody(), block))
                return true;

        }
        return false;
    }

    // TODO: test more complex cases
    private boolean hasSameBlockHelp(StatementBlock block1,
            StatementBlock block2) {
        boolean result = false;
        ProgramElement pE;
        for (int i = 0; i < block1.getChildCount() && !result; i++) {
            pE = block1.getChildAt(i);
            result = (pE instanceof StatementBlock) && ((pE.equals(block2))
                    || hasSameBlockHelp((StatementBlock) pE, block2));
        }
        return result;
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
