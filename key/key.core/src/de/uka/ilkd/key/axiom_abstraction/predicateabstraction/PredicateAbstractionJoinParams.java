package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.rule.join.procedures.JoinParams;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * TODO
 * 
 * XXX: Should probably be moved into another package.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionJoinParams extends JoinParams {
    /**
     * Pair of a predicate abstraction lattice type (simple, conjunctive,
     * disjunctive) and the textual specification of the predicates.
     */
    private final Pair<String, String> params;

    private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;
    private List<AbstractionPredicate> predicates;

    /**
     * TODO: This getter is probably not good design... We could alredy offer
     * the parsing here!
     * 
     * @param params
     */
    public PredicateAbstractionJoinParams(Pair<String, String> params) {
        super(JoinWithPredicateAbstraction.class);
        
        this.params = params;
        this.latticeType = latticeTypeFromString();
    }

    /**
     * TODO
     * 
     * @param services
     * @return
     */
    public List<AbstractionPredicate> getPredicates(Services services) {
        if (predicates == null) {
            predicates = parsePredicateSpec(params.second, services);
        }

        return predicates;
    }
    
    /**
     * 
     * TODO
     * @return
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    /**
     * TODO
     * @return
     */
    private Class<? extends AbstractPredicateAbstractionLattice> latticeTypeFromString() {
        switch (params.first) {
        case "simple": return SimplePredicateAbstractionLattice.class;
        case "conjunctive": return ConjunctivePredicateAbstractionLattice.class;
        case "disjunctive": return DisjunctivePredicateAbstractionLattice.class;
        default: throw new RuntimeException("PredicateAbstractionJoinParams: Unexpected lattice type.");
        }
    }

    /**
     * TODO
     * 
     * XXX: Make private, should only be accessed from the inside.
     * 
     * @param params
     * @param services
     * @return
     */
    static List<AbstractionPredicate> parsePredicateSpec(String params,
            Services services) {
        List<AbstractionPredicate> result = new ArrayList<AbstractionPredicate>();
        try {
            Pattern p = Pattern.compile("(.+?) *-> *\\{([^\\}]+?)\\}");
            Matcher m = p.matcher(params);
            while (m.find()) {
                for (int i = 1; i < m.groupCount(); i += 2) {

                    final String phStr = m.group(i);
                    final String[] predStr = m.group(i + 1).split(", ");

                    // Parse the placeholder
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

            }

        } catch (ParserException | JoinRuleUtils.SortNotKnownException e) {
            result = new ArrayList<AbstractionPredicate>();
            e.printStackTrace();
        }
        return result;
    }
}
