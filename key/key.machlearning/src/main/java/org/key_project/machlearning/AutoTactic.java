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

        ProofSettings settings = proof.getSettings();
        String savedProperties = settings.settingsToString();
        Properties properties = new Properties();
        properties.load(new StringReader(DEFAULT_SETTINGS + "\n" + additionalSettings));
        for (Settings s : settings.getSettings()) {
            s.readSettings(properties);
        }

        prover.start(proof, goal);

        // resetting settings
        settings.loadSettingsFromString(savedProperties);
    }
}
