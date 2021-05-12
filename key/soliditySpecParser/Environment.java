import java.util.*;

/* This class allows anyone to modify its member variables, but the
 * intention is to eventually disallow it and provide access only
 * through methods. 
 */
class Environment {
    public enum UnitType {CONTRACT, INTERFACE, LIBRARY}

    public Map<String,String> vars = new HashMap<>();
    public Map<String,String> cumulativeLogicalVars = new HashMap<>();
    public Map<String,Environment.FunctionInfo> funcs = new HashMap<>();
    public Set<String> enums = new HashSet<>();
    public Map<String,UserType> userTypes = new HashMap<>();
    public UnitType unitType;
    private Map<String,String> unqualifiedToQualified = new HashMap<>();

    public static class FunctionInfo {
        public boolean payable;
        public int lineNo;
        public Map<String,String> parameters = new HashMap<>();
        public List<String> parameterOrder = new LinkedList<>();
        public String returnType;
        public FunctionInfo(boolean p,int l) {
            payable = p;
            lineNo = l;
        }
        public FunctionInfo() {};
        public String toString() {
            return "payable " + payable + " line no " + lineNo;
        }
    }

    public static class UserType {
        public Map<String,String> members = new HashMap<>();
    }

    public void addFunctionParameter(String func, String ident, String type) {
        funcs.get(func).parameters.put(ident, qualify(type));
        funcs.get(func).parameterOrder.add(ident);

    }
/*
    public void addUserTypeVariableWithMembers(String instance, String userType) {
        for (Map.Entry<String,String> e : userTypes.get(userType).members.entrySet()) {
            vars.put(instance + "." + e.getKey(), e.getValue());
        }
    }

    public void removeUserTypeStateVarWithMembers(String instance, String userType) {
        for (Map.Entry<String,String> e : userTypes.get(userType).members.entrySet()) {
            vars.remove(instance + "." + e.getKey());
        }
    }*/

    public void addVariable(String ident, String type) {
        vars.put(ident, qualify(type));
    }

    public void removeVariable(String ident) {
        vars.remove(ident);
    }

    public String qualify(String type) {
        return unqualifiedToQualified.get(type) != null ? unqualifiedToQualified.get(type) : type;
    }

    public void addUserType(String ident, String superUnit, UserType ut) {
        userTypes.put(superUnit + "." + ident,ut);
        unqualifiedToQualified.put(ident, superUnit + "." + ident);
    }
}

