package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SolverType;

import javax.swing.*;

import static de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider.BUNDLE;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
class SolverOptions extends SettingsPanel implements SettingsProvider {
    private static final String infoSolverName = "infoSolverName";
    private static final String infoSolverParameters = "infoSolverParameters";
    private static final String infoSolverCommand = "infoSolverCommand";
    private static final String infoSolverSupport = "infoSolverSupport";
    private static final String[] solverSupportText = {
            BUNDLE.getString("SOLVER_SUPPORTED"),
            BUNDLE.getString("SOLVER_MAY_SUPPORTED"),
            BUNDLE.getString("SOLVER_UNSUPPORTED")};

    private static final int SOLVER_SUPPORTED = 0;

    private static final int SOLVER_NOT_SUPPOTED = 1;
    private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;
    private final SolverType solverType;
    private final JTextField solverCommand;
    private final JTextField solverParameters;
    private final JTextField solverSupported;
    private final JTextField solverName;
    private final JTextField solverInstalled;

    private ProofIndependentSMTSettings settings;

    public SolverOptions(SolverType solverType) {
        this.setName(solverType.getName());
        this.solverType = solverType;
        setHeaderText("SMT Solver: " + getDescription());

        solverName = createSolverName();
        solverInstalled = createSolverInstalled();
        solverCommand = createSolverCommand();
        solverParameters = createSolverParameters();
        solverSupported = createSolverSupported();
        createDefaultButton();
        createCheckSupportButton();
    }

    protected JButton createDefaultButton() {
        JButton toDefaultButton = new JButton("Set parameters to default.");
        toDefaultButton.addActionListener(arg0 -> {
            solverParameters.setText(solverType.getDefaultSolverParameters());
            settings.setParameters(solverType, solverParameters.getText());

        });
        addRowWithHelp(null, new JLabel(), toDefaultButton);
        return toDefaultButton;
    }

    private String createSupportedVersionText() {
        String[] versions = solverType.getSupportedVersions();
        String result = versions.length > 1 ? "The following versions are supported: " :
                "The following version is supported: ";
        for (int i = 0; i < versions.length; i++) {
            result += versions[i];
            result += i < versions.length - 1 ? ", " : "";
        }
        return result;
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion() ? solverSupportText[SOLVER_SUPPORTED] : solverSupportText[SOLVER_NOT_SUPPOTED];
        } else {
            return solverSupportText[SOLVER_SUPPORT_NOT_CHECKED];
        }
    }

    protected JTextField createSolverSupported() {

        JTextField txt = addTextField("Support", getSolverSupportText(),
                BUNDLE.getString(infoSolverSupport) + createSupportedVersionText(), null);
        txt.setEditable(false);
        return txt;
    }

    protected JButton createCheckSupportButton() {
        JButton checkForSupportButton = new JButton("Check for support.");
        checkForSupportButton.setEnabled(solverType.isInstalled(false));
        checkForSupportButton.addActionListener(arg0 -> {
            solverType.checkForSupport();
            solverSupported.setText(getSolverSupportText());
        });
        addRowWithHelp(null, new JLabel(), checkForSupportButton);
        return checkForSupportButton;
    }

    protected JTextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(), BUNDLE.getString(infoSolverParameters),
                e -> settings.setParameters(solverType, solverParameters.getText()));
    }

    public JTextField createSolverCommand() {
        return addTextField("Command",
                solverType.getSolverCommand(),
                BUNDLE.getString(infoSolverCommand), e -> settings.setCommand(solverType, solverCommand.getText()));
    }


    protected JTextField createSolverInstalled() {
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ") + versionString + ")";
        }
        JTextField txt = addTextField("Installed", info, "", null);
        //txt.setBackground(this.getBackground());
        txt.setEditable(false);
        return txt;
    }

    protected JTextField createSolverName() {
        JTextField txt = addTextField("Name", solverType.getName(), BUNDLE.getString(infoSolverName), null);
        //txt.setBackground(this.getBackground());
        txt.setEditable(false);
        return txt;
    }

    @Override
    public String getDescription() {
        return solverType.getName();
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        setSmtSettings(SettingsManager.getSmtPiSettings().clone());
        return this;
    }

    private void setSmtSettings(ProofIndependentSMTSettings clone) {
        settings = clone;
        solverCommand.setText(settings.getCommand(solverType));
        solverParameters.setText(settings.getParameters(solverType));

        solverName.setText(solverType.getName());
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ") + versionString + ")";
        }
        solverInstalled.setText(info);
    }

    @Override
    public void applySettings(MainWindow window) {
        solverType.setSolverCommand(settings.getCommand(solverType));
        solverType.setSolverParameters(settings.getParameters(solverType));
        SettingsManager.getSmtPiSettings().copy(settings);
        setSmtSettings(SettingsManager.getSmtPiSettings().clone());
    }
}
