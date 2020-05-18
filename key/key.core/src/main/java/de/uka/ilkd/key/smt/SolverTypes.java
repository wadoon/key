package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (5/18/20)
 */
public final class SolverTypes {
    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */
    public static final SolverType Z3_SOLVER = new AbstractSolverType() {
        public String getDefaultSolverCommand() {
            return "z3";
        }

        public String getDefaultSolverParameters() {
            return "-in -smt2";
        }

        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        @Override
        public String getName() {
            return "Z3";
        }

        public String getVersionParameter() {
            return "-version";
        }

        @Override
        public String getRawVersion() {
            final String tmp = super.getRawVersion();
            if (tmp == null) return null;
            return tmp.substring(tmp.indexOf("version"));
        }

        public String[] getSupportedVersions() {
            return new String[]{"version 3.2", "version 4.1", "version 4.3.0", "version 4.3.1"};
        }

        public String[] getDelimiters() {
            return new String[]{"\n", "\r"};
        }

        public boolean supportsIfThenElse() {
            return true;
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            return new SmtLib2Translator(services,
                    new AbstractSMTTranslator.Configuration(false, false));
        }

        @Override
        public String getInfo() {
            return "";
//                    return "Z3 does not use quantifier elimination by default. This means for example that"
//                                    + " the following problem cannot be solved automatically by default:\n\n"
//                                    + "\\functions{\n"
//                                    + "\tint n;\n"
//                                    + "}\n\n"
//                                    + "\\problem{\n"
//                                    + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
//                                    + "}"
//                                    + "\n\n"
//                                    + "You can activate quantifier elimination by appending QUANT_FM=true to"
//                                    + " the execution command.";
        }


    };
    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */
    public static final SolverType Z3_CE_SOLVER = new AbstractSolverType() {


        public String getDefaultSolverCommand() {
            return "z3";
        }

        public String getDefaultSolverParameters() {
            return "-in -smt2";
        }

        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        @Override
        public String getName() {
            return "Z3_CE";
        }

        public String getVersionParameter() {
            return "-version";
        }

        public String[] getSupportedVersions() {
            return new String[]{"version 4.3.1"};
        }

        public String[] getDelimiters() {
            return new String[]{"\n", "\r"};
        }

        public boolean supportsIfThenElse() {
            return true;
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            return new SmtLib2Translator(services,
                    new AbstractSMTTranslator.Configuration(false, false));
        }


        @Override
        public String getInfo() {
            return "";
            //                        return "Z3 does not use quantifier elimination by default. This means for example that"
            //                                        + " the following problem cannot be solved automatically by default:\n\n"
            //                                        + "\\functions{\n"
            //                                        + "\tint n;\n"
            //                                        + "}\n\n"
            //                                        + "\\problem{\n"
            //                                        + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
            //                                        + "}"
            //                                        + "\n\n"
            //                                        + "You can activate quantifier elimination by appending QUANT_FM=true to"
            //                                        + " the execution command.";
        }


    };
    /**
     * Class for the CVC3 solver. It makes use of the SMT1-format.
     */
    public static final SolverType CVC3_SOLVER = new AbstractSolverType() {

        @Override
        public String getName() {
            return "CVC3";
        }

        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        public String getDefaultSolverCommand() {
            return "cvc3";
        }

        private boolean useNewVersion() {
            final String solverVersion = getRawVersion();
            return "version 2.4.1".equals(solverVersion);
        }

        @Override
        public String getRawVersion() {
            final String tmp = super.getRawVersion();
            if (tmp == null) return null;
            return tmp.substring(tmp.indexOf("version"));
        }

        @Override
        public String getDefaultSolverParameters() {
            // version 2.4.1 uses different parameters
            if (useNewVersion())
                return "-lang smt +model +interactive";
                //                      return "-lang smt2 +model +interactive";
            else
                return "+lang smt +model +int";
        }

        public String[] getDelimiters() {
            return new String[]{"CVC>", "C>"};
        }

        public String[] getSupportedVersions() {
            return new String[]{"version 2.2", "version 2.4.1"};
        }

        public String getVersionParameter() {
            return "-version";
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            final AbstractSMTTranslator.Configuration conf = new AbstractSMTTranslator.Configuration(false, true);
            //                    if (useNewVersion())
            //                        return new SmtLib2Translator(services, conf);
            //                    else
            return new SmtLibTranslator(services, conf);
        }

        public boolean supportsIfThenElse() {
            return true;
        }

        @Override
        public String getInfo() {
            return null;
        }


    };
    /**
     * CVC4 is the successor to CVC3.
     *
     * @author bruns
     */
    public static final SolverType CVC4_SOLVER = new AbstractSolverType() {

        // TODO move to AbstractSolverType?
        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        @Override
        public String getName() {
            return "CVC4";
        }

        @Override
        public String getInfo() {
// todo Auto-generated method stub
            return null;
        }

        @Override
        public String getDefaultSolverParameters() {
            return "--no-print-success -m --interactive --lang smt2";
        }

        @Override
        public String getDefaultSolverCommand() {
            return "cvc4";
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            final AbstractSMTTranslator.Configuration conf = new AbstractSMTTranslator.Configuration(false, true);
            return new SmtLib2Translator(services, conf);
        }

        @Override
        public String[] getDelimiters() {
            return new String[]{"CVC4>"};
        }

        @Override
        public boolean supportsIfThenElse() {
            return true;
        }

        @Override
        public String getVersionParameter() {
            return "--version";
        }

        @Override
        public String[] getSupportedVersions() {
            return new String[]{"version 1.3"};
        }

    };
    /**
     * Class for the Yices solver. It makes use of the SMT1-format.
     */
    public static final SolverType YICES_SOLVER = new AbstractSolverType() {

        @Override
        public String getName() {
            return "Yices";
        }

        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            return new SmtLibTranslator(services,
                    new AbstractSMTTranslator.Configuration(true, true));
        }


        @Override
        public String getDefaultSolverCommand() {
            return "yices";
        }

        public String[] getDelimiters() {
            return new String[]{"\n", "\r"};
        }

        @Override
        public String getDefaultSolverParameters() {
            return "-i -e -smt";
        }


        public String getVersionParameter() {
            return "--version";
        }

        public String[] getSupportedVersions() {
            return new String[]{"1.0.34"};
        }

        @Override
        public String getInfo() {
            return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the "
                    + "required logic AUFLIA.";
        }

        public boolean supportsIfThenElse() {
            return true;
        }


        public String modifyProblem(String problem) {
            return problem += "\n\n check\n";
        }

    };
    /**
     * Class for the Simplify solver. It makes use of its own format.
     */
    public static final SolverType SIMPLIFY_SOLVER = new AbstractSolverType() {


        @Override
        public String getName() {
            return "Simplify";
        }

        @Override
        public SMTSolver createSolver(SMTProblem problem,
                                      SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                    services, this);
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            return new SimplifyTranslator(services,
                    new AbstractSMTTranslator.Configuration(false, true));
        }

        public String getDefaultSolverCommand() {
            return "simplify";
        }

        public String[] getSupportedVersions() {
            return new String[]{"version 1.5.4"};
        }

        @Override
        public String getRawVersion() {
            final String tmp = super.getRawVersion();
            if (tmp == null) return null;
            return tmp.substring(tmp.indexOf("version"));
        }

        public String[] getDelimiters() {
            return new String[]{">"};
        }

        public String getDefaultSolverParameters() {
            return "-print";
        }


        public String getVersionParameter() {
            return "-version";
        }


        @Override
        public String getInfo() {
            return "Simplify only supports integers within the interval [-2147483646,2147483646]=[-2^31+2,2^31-2].";
        }

        public boolean supportsIfThenElse() {
            return false;
        }


    };

    public static final List<SolverType> ALL_SOLVERS =
            Collections.unmodifiableList(Arrays.asList(
                    Z3_SOLVER,
                    CVC3_SOLVER,
                    SIMPLIFY_SOLVER,
                    YICES_SOLVER
            ));

    SolverTypes() {
    }
}
