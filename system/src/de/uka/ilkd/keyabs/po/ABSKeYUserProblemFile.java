package de.uka.ilkd.keyabs.po;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DeclPicker;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.CountingBufferedReader;
import de.uka.ilkd.key.proof.IProofFileParser;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.init.io.ABSKeYFile;
import de.uka.ilkd.keyabs.parser.ABSKeYLexer;
import de.uka.ilkd.keyabs.parser.ABSKeYParser;

public class ABSKeYUserProblemFile extends ABSKeYFile implements ProofOblInput {

    private Term problemTerm = null;
    private String problemHeader = "";

    private ABSKeYParser lastParser;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a new representation of a KeYUserFile with the given name, a rule
     * source representing the physical source of the input, and a graphical
     * representation to call back in order to report the progress while
     * reading.
     */
    public ABSKeYUserProblemFile(String name, File file, ProgressMonitor monitor) {
        super(name, file, monitor);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ABSKeYUserProblemFile)) {
            return false;
        }
        final ABSKeYUserProblemFile kf = (ABSKeYUserProblemFile) o;
        return kf.file.file().getAbsolutePath()
                .equals(file.file().getAbsolutePath());
    }

    @Override
    public ProofAggregate getPO() throws ProofInputException {
        assert problemTerm != null;
        String name = name();
        ProofSettings settings = getPreferences();
        return ProofAggregate.createProofAggregate(
                new Proof(name, problemTerm, problemHeader, initConfig
                        .createTacletIndex(), initConfig
                        .createBuiltInRuleIndex(), initConfig.getServices(),
                        settings), name);
    }

    @Override
    public int hashCode() {
        return file.file().getAbsolutePath().hashCode();
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }

    @Override
    public void read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }

        // read activated choices
        try {
            ProofSettings settings = getPreferences();

            ParserConfig<ABSServices> pc = new ParserConfig<ABSServices>(
                    initConfig.getServices(), initConfig.namespaces());
            ABSKeYParser problemParser = new ABSKeYParser(ParserMode.PROBLEM,
                    new ABSKeYLexer(getNewStream(), initConfig.getServices()
                            .getExceptionHandler()), file.toString(), pc, pc,
                    null, null);
            problemParser.parseWith();

            settings.getChoiceSettings().updateWith(
                    problemParser.getActivatedChoices());

            initConfig.setActivatedChoices(settings.getChoiceSettings()
                    .getDefaultChoicesAsSet());

        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        } catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }

        // read in-code specifications

        /*
         * SLEnvInput slEnvInput = new SLEnvInput(readJavaPath(),
         * readClassPath(), readBootClassPath());
         * slEnvInput.setInitConfig(initConfig); slEnvInput.read();
         */

        // read key file itself
        super.read();
    }

    @Override
    public void readProblem() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException(
                    "KeYUserProblemFile: InitConfig not set.");
        }

        try {
            CountingBufferedReader cinp = new CountingBufferedReader(
                    getNewStream(), monitor, getNumberOfChars() / 100);
            DeclPicker lexer = new DeclPicker(new ABSKeYLexer(cinp, initConfig
                    .getServices().getExceptionHandler()));

            final ParserConfig<ABSServices> normalConfig = new ParserConfig<ABSServices>(
                    initConfig.getServices(), initConfig.namespaces());
            final ParserConfig<ABSServices> schemaConfig = new ParserConfig<ABSServices>(
                    initConfig.getServices(), initConfig.namespaces());

            ABSKeYParser problemParser = new ABSKeYParser(ParserMode.PROBLEM,
                    lexer, file.toString(), schemaConfig, normalConfig,
                    initConfig.getTaclet2Builder(), initConfig.getTaclets());
            problemTerm = problemParser.parseProblem();
            String searchS = "\\problem";

            if (problemTerm == null) {
                boolean chooseDLContract = problemParser.getChooseContract() != null;
                if (chooseDLContract)
                    searchS = "\\chooseContract";
                else {
                    cinp.close();
                    throw new ProofInputException(
                            "No \\problem or \\chooseContract in the input file!");
                }
            }

            problemHeader = lexer.getText();
            if (problemHeader != null
                    && problemHeader.lastIndexOf(searchS) != -1) {
                problemHeader = problemHeader.substring(0,
                        problemHeader.lastIndexOf(searchS));
            }
            initConfig.setTaclets(problemParser.getTaclets());
            lastParser = problemParser;
        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        } catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        } catch (IOException e) {
            throw new ProofInputException(e);
        }
    }

    /**
     * Reads a saved proof of a .key file.
     */
    public void readProof(IProofFileParser prl) throws ProofInputException {
        if (lastParser == null) {
            readProblem();
        }
        try {
            lastParser.proof(prl);
        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        }
    }

}
