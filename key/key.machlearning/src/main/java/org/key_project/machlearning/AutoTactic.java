package org.key_project.machlearning;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.GoalChooserBuilder;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.Settings;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import org.json.simple.JSONObject;

import java.io.StringReader;
import java.util.Properties;

public class AutoTactic implements Tactic {

    private static final String DEFAULT_SETTINGS =
                    "[StrategyProperty]DEP_OPTIONS_KEY=DEP_OFF\n" +
                    "[StrategyProperty]QUERYAXIOM_OPTIONS_KEY=QUERYAXIOM_OFF\n" +
                    "[StrategyProperty]CLASSAXIOM_OPTIONS_KEY=CLASSAXIOM_OFF\n" +
                    "[StrategyProperty]QUANTIFIERS_OPTIONS_KEY=QUANTIFIERS_NONE";


    private String additionalSettings;

    public AutoTactic(String additionalSettings) {
        this.additionalSettings = additionalSettings;
    }

    @Override
    public void apply(AbstractMediatorUserInterfaceControl ui, Proof proof, Goal goal, JSONObject command) throws Exception {
        Profile profile = proof.getInitConfig().getProfile();
        GoalChooser chooser = profile.getSelectedGoalChooserBuilder().create();
        ProverCore prover = new ApplyStrategy(chooser);

        Properties properties = new Properties();
        properties.load(new StringReader(DEFAULT_SETTINGS + "\n" + additionalSettings));
        StrategyProperties strategyProperties = StrategyProperties.read(properties);
        Strategy oldStrategy = proof.getActiveStrategy();
        Strategy newStratgy = proof.getActiveStrategyFactory().create(proof, strategyProperties);

        proof.setActiveStrategy(newStratgy);
        prover.start(proof, goal);

        // resetting settings
        proof.setActiveStrategy(oldStrategy);
    }
}
