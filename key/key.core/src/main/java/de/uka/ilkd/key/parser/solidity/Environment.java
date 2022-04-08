package de.uka.ilkd.key.parser.solidity;

import java.util.*;

class Environment {
    public Map<String,Solidity.Contract> contracts = new HashMap<>(); // Contract name => Contract
    public Map<String,Solidity.LogicalVariable> cumulativeLogicalVars = new HashMap<>(); // Name => Variable
    public Map<String, Solidity.LogicalVariable> currentLogicalVars = new HashMap<>();
    public List<Solidity.Struct> freeStructs = new LinkedList<>();

    void addLogicalVar(String name, String type) {
        Solidity.LogicalVariable var = new Solidity.LogicalVariable(name, type);
        cumulativeLogicalVars.put(var.name, var);
        currentLogicalVars.put(var.name, var);
    }

    void removeLogicalVar(String name) {
        currentLogicalVars.remove(name);
    }

    /**
     * Lookup a field from a supposed field name 'fieldName', if the reference is found inside contract
     * 'startingContract'. We look for the field not only in the starting contract, but also in its parents.
     * @param fieldName The name of the field
     * @param startingContract The contract which to start looking for the field.
     * @return The field, if it was found, else null.
     */
    public Solidity.Field lookupField(String fieldName, Solidity.Contract startingContract) {
        Iterator<Solidity.Contract> it = startingContract.c3Linearization.descendingIterator();
        while (it.hasNext()) {
            Solidity.Contract parent = it.next();
            for (Solidity.Field field : parent.fields) {
                if (field.name.equals(fieldName))
                    return field;
            }
        }
        return null;
    }

    public Solidity.Modifier lookupModifier(String modName, Solidity.Contract startingContract) {
        // Note: modifiers cannot be overloaded with different argument lists.
        Iterator<Solidity.Contract> it = startingContract.c3Linearization.descendingIterator();
        while (it.hasNext()) {
            Solidity.Contract parent = it.next();
            for (Solidity.Modifier mod : parent.modifiers) {
                if (mod.name.equals(modName))
                    return mod;
            }
        }
        return null;
    }

    Solidity.Enum lookupEnum(String enumName, Solidity.Contract startingContract) {
    /*
        contract A { enum E {e} }
        contract B is A {
            function foo() public {
                A a = new A();
                E e1 = E.e; // allowed
                A.E e2 = A.E.e; // allowed
                a.E e3 = A.E.e; // disallowed
            }
        }
        contract C {
            function foo() public {
                A a = new A();
                E e1 = E.e; // disallowed
                A.E e2 = A.E.e; // allowed
                B.E e3 = B.E.e; // disallowed
            }
        }
		*/
        int dotPos = enumName.indexOf(".");
        if (dotPos == -1) {
            Iterator<Solidity.Contract> it = startingContract.c3Linearization.descendingIterator();
            while (it.hasNext()) {
                Solidity.Contract parent = it.next();
                for (Solidity.Enum enum_ : parent.enums) {
                    if (enum_.name.equals(enumName))
                        return enum_;
                }
            }
        } else {
            Solidity.Contract contract = contracts.get(enumName.substring(0, dotPos));
            if (contract == null) {
                return null;
            }
            return contract.getEnum(enumName.substring(dotPos + 1));
        }
        return null;
    }

    Solidity.Struct lookupStruct(String structName, Solidity.Contract startingContract) {
        // Similar rules as for enums
        int dotPos = structName.indexOf(".");
        if (dotPos == -1) {
            Iterator<Solidity.Contract> it = startingContract.c3Linearization.descendingIterator();
            while (it.hasNext()) {
                Solidity.Contract parent = it.next();
                for (Solidity.Struct struct : parent.structs) {
                    if (struct.name.equals(structName))
                        return struct;
                }
            }
            for (Solidity.Struct struct : freeStructs) {
                if (struct.name.equals(structName)) {
                    return struct;
                }
            }
        } else {
            Solidity.Contract contract = contracts.get(structName.substring(0, dotPos));
            if (contract == null) {
                return null;
            }
            return contract.getStruct(structName.substring(dotPos + 1));
        }
        return null;
    }
}