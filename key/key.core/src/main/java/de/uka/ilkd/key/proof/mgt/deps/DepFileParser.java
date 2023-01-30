package de.uka.ilkd.key.proof.mgt.deps;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

import java.util.HashMap;
import java.util.Map;

/**
 * A parser for dependency files
 */
public class DepFileParser {
    /**
     * The registered services
     */
    private final Services services;
    /**
     * The tokenizer for the current input
     */
    private DepFileTokenizer tokenizer;
    /**
     * The current token
     */
    private DepFileTokenizer.Token current = null;

    public DepFileParser(Services services) {
        this.services = services;
    }

    /**
     * Parse the input for the folder of folder path
     * @param folderPath Path to the folder for which we parse the file
     * @param in The content of the file
     * @return Parsed dependency information
     * @throws DepFileParserException if the file does not fit the grammar
     */
    public DependencyInformation parse(String folderPath, String in) throws DepFileParserException {
        tokenizer = new DepFileTokenizer(in);
        return parseDepInfo(folderPath);
    }

    /**
     * Entry parse method
     * @param folderName Path to the folder for which we parse the file
     * @return Parsed dependency information
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private DependencyInformation parseDepInfo(String folderName) throws DepFileParserException {
        Map<String, FileDependencyInformation> fileInfos = new HashMap<>();
        while (current != null || tokenizer.hasNext()) {
            FileDependencyInformation fdi = parseFileInfo();
            fileInfos.put(fdi.getFilePath(), fdi);
        }
        return new DependencyInformation(folderName, fileInfos);
    }

    /**
     * Parses dependency info for a file in the folder
     * @return Dependency info for a file in the folder
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private FileDependencyInformation parseFileInfo() throws DepFileParserException {
        String filePath = parseFilePath();
        eat(DepFileTokenizer.TokenType.L_BRACE);
        FileDependencyInformation fdi = new FileDependencyInformation(filePath);
        while (!isCurrentOfType(DepFileTokenizer.TokenType.R_BRACE)) {
            ContractInfo ci = parseContractInfo();
            Contract c = services.getSpecificationRepository().getContractByName(ci.getName());
            // For this contract if either changes we must re-verify and reset dependencies
            boolean cChanged = isContractSpecificationChanged(c, ci) || isContractImplementationChanged(c, ci);
            eat(DepFileTokenizer.TokenType.L_BRACE);
            while (!isCurrentOfType(DepFileTokenizer.TokenType.R_BRACE)) {
                ContractInfo di = parseContractInfo();
                Contract d = services.getSpecificationRepository().getContractByName(di.getName());
                // The implementation of this can change, but the specification must stay the same
                boolean dChanged = isContractSpecificationChanged(d, di);
                if (!cChanged && !dChanged) {
                    fdi.addDep(c, d);
                }
            }
            eat();
        }
        eat();
        return fdi;
    }

    /**
     * @return Contract info (name and hashes)
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private ContractInfo parseContractInfo() throws DepFileParserException {
        String contractName = parseContractName();
        eat(DepFileTokenizer.TokenType.VERT_DASH);
        int contractHash = parseHash();
        if (isCurrentOfType(DepFileTokenizer.TokenType.VERT_DASH)) {
            eat();
            int implHash = parseHash();
            return new ContractInfo(contractName, contractHash, implHash);
        }
        return new ContractInfo(contractName, contractHash);
    }

    /**
     * @return Name of a contract
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private String parseContractName() throws DepFileParserException {
        expect(DepFileTokenizer.TokenType.CONTRACT_NAME);
        String name = getCurrent().getSpelling();
        eat();
        return name;
    }

    /**
     * @return Path to file
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private String parseFilePath() throws DepFileParserException {
        expect(DepFileTokenizer.TokenType.FILE_PATH);
        String name = getCurrent().getSpelling();
        eat();
        return name;
    }

    /**
     * @return A hash
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private int parseHash() throws DepFileParserException {
        expect(DepFileTokenizer.TokenType.NUMBER);
        String name = getCurrent().getSpelling();
        eat();
        return Integer.parseInt(name);
    }

    /**
     * Throw exception if we encounter unexpected token
     * @param expected Expected type
     * @throws DepFileParserException if the file does not fit the grammar
     */
    private void expect(DepFileTokenizer.TokenType expected) throws DepFileParserException {
        if (!isCurrentOfType(expected)) {
            throw new DepFileParserException("Expected '" + expected + "' but got '" + getCurrent().getSpelling());
        }
    }

    /**
     * @param expected The expected type for the current token
     * @return Whether the current token is of type <code>expected</code>
     * @throws DepFileParserException if there is an unexpected end of file
     */
    private boolean isCurrentOfType(DepFileTokenizer.TokenType expected) throws DepFileParserException {
        checkForNextToken();
        return getCurrent().getType().equals(expected);
    }

    /**
     * Advance to next token
     * @throws DepFileParserException if there is an unexpected end of file
     */
    private void eat() throws DepFileParserException {
        checkForNextToken();
        current = tokenizer.next();
    }

    /**
     * Advance to next token if the current token fits <code>expected</code>
     * @param expected The expected type for the current token
     * @throws DepFileParserException if the current token does not fit the exptected type
     */
    private void eat(DepFileTokenizer.TokenType expected) throws DepFileParserException {
        expect(expected);
        eat();
    }

    /**
     * @return The current token
     * @throws DepFileParserException if there is an unexpected end of file
     */
    private DepFileTokenizer.Token getCurrent() throws DepFileParserException {
        if (current == null) {
            checkForNextToken();
            current = tokenizer.next();
        }
        return current;
    }

    /**
     * @throws DepFileParserException if there is an unexpected end of file
     */
    private void checkForNextToken() throws DepFileParserException {
        if (current == null && !tokenizer.hasNext()) {
            throw new DepFileParserException("Expected another token but got EOF");
        }
    }

    /**
     * @param c Contract
     * @param ci Contract information
     * @return Whether the contract has changed, i.e., c fits ci
     */
    private boolean isContractSpecificationChanged(Contract c, ContractInfo ci) {
        if (c == null) {
            // Contract no longer exists, we must not track dependencies of and on it
            return true;
        }
        int oldSpecHash = ci.getSpecificationHash();
        int currentSpecHash = services.getContractDependencyRepository().getSpecificationHash(c);
        // Specification changed
        return oldSpecHash != currentSpecHash;
    }

    /**
     * @param c Contract
     * @param ci Contract information
     * @return Whether the contract's implementation has changed
     */
    private boolean isContractImplementationChanged(Contract c, ContractInfo ci) {
        if (c == null) {
            // Contract no longer exists, we must not track dependencies of and on it
            return true;
        }
        if (ci.hasImplementationHash) {
            int oldImplHash = ci.getImplementationHash();
            int currentImplHash = services.getContractDependencyRepository().getImplementationHash(c);
            // Implementation has changed
            return oldImplHash != currentImplHash;
        }

        if (services.getContractDependencyRepository().hasImplementation(c)) {
            // The contract in the file has an implementation, but the currently loaded one doesn't
            return true;
        }
        return false;
    }

    /**
     * The name, specification hash, and implementation hash saved in a dependency file
     */
    private static class ContractInfo {
        /**
         * Name of the contract
         */
        private final String name;
        /**
         * Hash of the specification's plaintext
         */
        private final int specificationHash;
        /**
         * Hash of the pretty printed implementation
         */
        public final int implementationHash;
        /**
         * Whether the contract has an implementation hash at all
         */
        private final boolean hasImplementationHash;

        public ContractInfo(String name, int specificationHash) {
            this.name = name;
            this.specificationHash = specificationHash;
            this.implementationHash = 0;
            this.hasImplementationHash = false;
        }

        public ContractInfo(String name, int specificationHash, int implementationHash) {
            this.name = name;
            this.specificationHash = specificationHash;
            this.implementationHash = implementationHash;
            this.hasImplementationHash = true;
        }

        public String getName() {
            return name;
        }

        public int getSpecificationHash() {
            return specificationHash;
        }

        public int getImplementationHash() {
            return implementationHash;
        }
    }
}
