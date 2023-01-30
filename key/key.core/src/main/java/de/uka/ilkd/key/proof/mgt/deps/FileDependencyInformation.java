package de.uka.ilkd.key.proof.mgt.deps;

import de.uka.ilkd.key.speclang.Contract;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Stores the dependency information for a Java file
 */
public class FileDependencyInformation {
    /**
     * Path to the Java file
     */
    private final String filePath;
    /**
     * Dependencies of contracts in the file
     */
    private final HashMap<Contract, Set<Contract>> contractDeps;

    public FileDependencyInformation(String filePath) {
        this.filePath = filePath;
        this.contractDeps = new HashMap<>();
    }

    public String getFilePath() {
        return filePath;
    }

    public Set<Contract> getContracts() {
        return contractDeps.keySet();
    }

    public Set<Contract> getDependencies(Contract c) {
        return contractDeps.get(c);
    }

    public Set<Map.Entry<Contract, Set<Contract>>> getContractDependencies() {
        return contractDeps.entrySet();
    }

    /**
     * Add dependency
     * @param addTo The contract which depends
     * @param toAdd The contract depended on
     * @return <code>true</code> if dependency is new
     */
    public boolean addDep(Contract addTo, Contract toAdd) {
        if (!contractDeps.containsKey(addTo)) {
            contractDeps.put(addTo, new HashSet<>());
        }
        return contractDeps.get(addTo).add(toAdd);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(filePath);
        sb.append("{ ");
        for (Map.Entry<Contract, Set<Contract>> entry : contractDeps.entrySet()) {
            printEntry(sb, entry);
        }
        sb.append(" }");
        return sb.toString();
    }

    private void printEntry(StringBuilder sb, Map.Entry<Contract, Set<Contract>> entry) {
        sb.append(entry.getKey().getName());
        sb.append(" -> ");
        sb.append('{');
        for (Contract c : entry.getValue()) {
            sb.append(c.getName());
            sb.append(',');
        }
        sb.append('}');
        sb.append('\n');
    }
}
