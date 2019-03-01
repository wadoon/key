package edu.kit.iti.formal.psdbg;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;


public class RuleCommandHelper {
    private final Proof proof;
    private final Services services;
    private final Goal g;
    private final RuleCommand.Parameters parameters;

    public RuleCommandHelper(Goal g, RuleCommand.Parameters parameters) {
        this.proof = g.proof();
        this.services = proof.getServices();
        this.g = g;
        this.parameters = parameters;
    }

    public int getOccurence(TacletApp app) {
        List<TacletApp> apps = getTacletApps();

        if (apps.isEmpty()) {
            return -1;
        }

        if(apps.size()==1) {
            return 0;
        }

        return 0;
        //return apps.indexOf(app);
    }

    private List<TacletApp> getTacletApps() {
        ImmutableList<TacletApp> allApps = findAllTacletApps();
        return filterList(allApps);
    }

    public ImmutableList<TacletApp> findAllTacletApps() {
        TacletFilter filter = new TacletNameFilter(parameters.rulename);
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (parameters.formula != null && !sf.formula().equalsModRenaming(parameters.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (parameters.formula != null && !sf.formula().equalsModRenaming(parameters.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                    services));
        }

        return allApps;
    }

    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private List<TacletApp> filterList(ImmutableList<TacletApp> list) {
        List<TacletApp> matchingApps = new ArrayList<TacletApp>();
        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if (parameters.on == null || pta.posInOccurrence().subTerm()
                        .equalsModRenaming(parameters.on)) {
                    matchingApps.add(pta);
                }
            }
        }
        return matchingApps;
    }


    private static class TacletNameFilter extends TacletFilter {
        private final Name rulename;

        public TacletNameFilter(String rulename) {
            this.rulename = new Name(rulename);
        }

        @Override
        protected boolean filter(Taclet taclet) {
            return taclet.name().equals(rulename);
        }
    }

}
