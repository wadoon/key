package de.uka.ilkd.key.parser.solidity;

import java.util.*;

class Environment {
    public Map<String,Solidity.Contract> contracts = new HashMap<>(); // Contract name => Contract
    public Map<String,Solidity.LogicalVariable> cumulativeLogicalVars = new HashMap<>(); // Name => Variable
    public Map<String, Solidity.LogicalVariable> currentLogicalVars = new HashMap<>();
    public List<Solidity.Function> freeFunctions = new LinkedList<>(); // TODO: yet to be populated
    public List<Solidity.Struct> freeStructs = new LinkedList<>(); // TODO: yet to be populated
    public List<Solidity.Variable> freeConstants = new LinkedList<>(); // TODO: yet to be populated

    void addLogicalVar(String name, String type) {
        Solidity.LogicalVariable var = new Solidity.LogicalVariable(name, type);
        cumulativeLogicalVars.put(var.name, var);
        currentLogicalVars.put(var.name, var);
    }

    void removeLogicalVar(String name) {
        currentLogicalVars.remove(name);
    }
}