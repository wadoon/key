import java.util.*;

class Environment {
    public Map<String,String> vars = new HashMap<>();
    public Map<String,String> cumulativeLogicalVars = new HashMap<>();
    public Map<String,Environment.FunctionInfo> funcs = new HashMap<>();
    public Set<String> enums = new HashSet<>();

    public static class FunctionInfo {
        public boolean payable;
        public int lineNo;
        public Map<String,String> parameters = new HashMap<>();
        public List<String> parameterOrder = new LinkedList<>();
        public FunctionInfo(boolean p,int l) {
            payable = p;
            lineNo = l;
        }
        public FunctionInfo() {};
        public String toString() {
            return "payable " + payable + " line no " + lineNo;
        }
    }
}

