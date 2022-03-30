package de.uka.ilkd.key.parser.solidity;

import java.util.*;

public class ProofObligations {
    public String invariant;
    public String libInvariantTemplate;
    public Map<String,FunctionProofObligations> posMap = new HashMap<>();

    private FunctionProofObligations getFPO(String function) {
        if (posMap.get(function) == null) {
            posMap.put(function, new FunctionProofObligations());
        }
        return posMap.get(function);
    }

    public void addAssumes(String function, String a) {
        getFPO(function).addAssumes(a);
    }

    public void addOnlyIf(String function, String oi) {
        getFPO(function).addOnlyIf(oi);
    }

    public void addOnSuccess(String function, String os) {
        getFPO(function).addOnSuccess(os);
    }

    public void addAssignable(String function, String a) {
        getFPO(function).addAssignable(a);
    }

    public void addInvariant(String i) {
        invariant = invariant == null ? i : invariant + " & " + i;
    }

    public void setLibraryInvariant(String i) {
        libInvariantTemplate = i;
    }

    public boolean isGross(String function) {
        return getFPO(function).isGross();
    }

    public void setGross(String function, boolean g) {
        getFPO(function).setGross(g);
    }
}
