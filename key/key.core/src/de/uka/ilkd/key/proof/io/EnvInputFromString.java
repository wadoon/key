package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.PositionedString;

public class EnvInputFromString extends AbstractKeYParserEnvInput implements ProofOblInput {

    private final String problem;

    public EnvInputFromString(String problem) {
        this.problem = problem;
    }

    public String name() {
        return EnvInputFromString.class.getName() + " " + problem.hashCode();
    }

    @Override
    public int getNumberOfChars() {
        return problem.length();
    }

    @Override
    public String readJavaPath() throws ProofInputException {
        return null;
    }

    @Override
    public List<File> readClassPath() throws ProofInputException {
        return null;
    }

    @Override
    public File readBootClassPath() throws IOException {
        return null;
    }

    @Override
    public File getInitialFile() {
        return null;
    }

    @Override
    protected KeYLexerF getKeYLexer() {
        return new KeYLexerF(problem);
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }

    @Override
    public KeYJavaType getContainerType() {
        return null;
    }

    @Override
    public void readProblem() throws ProofInputException {
        readProblem(getKeYLexer());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getProfile() {
        return readProfileFromData();
    }

    @Override
    public void closeLexerStream() throws ProofInputException {
        // The data used in this class is based on strings and not on streams,
        // so closing is not necessary.
    }

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        return read(getKeYLexer());
    }

}
