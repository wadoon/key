import java.util.*;

class Environment {
    public enum UnitType {CONTRACT, INTERFACE, LIBRARY}

    public Map<String,String> vars = new HashMap<>();
    public Map<String,String> cumulativeLogicalVars = new HashMap<>();
    public Map<String,Environment.FunctionInfo> funcs = new HashMap<>();
    public Set<String> enums = new HashSet<>();
    public Map<String,UserType> userTypes = new HashMap<>();
    public UnitType unitType;

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
}

