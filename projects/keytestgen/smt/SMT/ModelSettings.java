package com.csvanefalk.keytestgen.core.model.implementation.SMT;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;
import de.uka.ilkd.key.smt.SMTSettings;

import java.io.File;
import java.util.Collection;

/**
 * Settings to pass to the SMT solver.
 *
 * @author christopher
 */
class DefaultSMTSettings implements SMTSettings {

    @Override
    public boolean checkForSupport() {

        return false;
    }

    @Override
    public String getLogic() {

        return "QF_UFLIRA";
        // return "AUFLIA";
    }

    @Override
    public int getMaxConcurrentProcesses() {

        return 1;
    }

    @Override
    public long getMaximumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
    }

    @Override
    public int getMaxNumberOfGenerics() {

        return 2;
    }

    @Override
    public long getMinimumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
    }

    @Override
    public String getSMTTemporaryFolder() {

        return PathConfig.getKeyConfigDir() + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets() {

        return null;
    }

    @Override
    public long getTimeout() {

        return 5000;
    }

    @Override
    public boolean instantiateNullAssumption() {

        return true;
    }

    @Override
    public boolean makesUseOfTaclets() {

        return false;
    }

    @Override
    public boolean useAssumptionsForBigSmallIntegers() {

        return false;
    }

    @Override
    public boolean useBuiltInUniqueness() {

        return false;
    }

    @Override
    public boolean useExplicitTypeHierarchy() {

        return false;
    }

    @Override
    public boolean useUninterpretedMultiplicationIfNecessary() {

        return false;
    }
}

/**
 * Settings for the model generation subsystem of KeYTestGen.
 *
 * @author christopher
 */
final class ModelSettings {

    /**
     * The default SMT settings to be used with an SMT solver used by
     * KeYTestGen.
     */
    private static final DefaultSMTSettings DEFAULT_SMT_SETTINGS = new DefaultSMTSettings();

    /**
     * The default settings for the SMTLIB translator.
     */
    private static final Configuration DEFAULT_TRANSLATOR_CONFIGURATION = new Configuration(
            false, true);

    /**
     * The number of times to re-try solving an SMT problem in the event that
     * "UNKNOWN" is returned, since this usually seems to point to an error
     * during the execution of the solver, rather than the problem not being
     * solveable.
     */
    private static final int NUMBER_OF_TRIES = 10;

    /**
     * @return the DEFAULT_SMT_SETTINGS constant, containing a default set of
     *         settings for SMT solvers used by KeYTestGen.
     */
    public static DefaultSMTSettings getDefaultSMTSettings() {
        return ModelSettings.DEFAULT_SMT_SETTINGS;
    }

    public static Configuration getDefaultTranslatorConfiguration() {
        return ModelSettings.DEFAULT_TRANSLATOR_CONFIGURATION;
    }

    /**
     * @return the NUMBER_OF_TRIES constant, dictating how many times a Model
     *         Generator should re-attempt to solve an SMT problem whose last
     *         known solution was UNKNOWN.
     */
    public static int getNUMBER_OF_TRIES() {
        return ModelSettings.NUMBER_OF_TRIES;
    }
}