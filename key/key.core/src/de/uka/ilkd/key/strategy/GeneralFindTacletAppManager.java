package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;

public interface GeneralFindTacletAppManager {

    boolean isResponsible(RuleAppContainer c);

    void add(RuleAppContainer c);

    Iterable<RuleAppContainer> getMatchingRuleApps(Goal goal);

}
