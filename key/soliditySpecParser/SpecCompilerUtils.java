import java.util.*;

public class SpecCompilerUtils {

    public enum HeapType {
        HEAP("heap"), OLD_HEAP("savedHeap"), HEAP_H("h");

        private String str;
        HeapType(String str) {this.str = str;}
        public String toString() {return str;}
    };

    public static String solidityToJavaType(String solType) {
        String ret;
        switch (solType) {
            case "uint":
            case "uint256":
                ret = "int";
                break;
            case "bool":
                ret = "boolean";
                break;
            case "address":
                ret = "Address";
                break;
            default:
                ret = solType;
                break;
        }
        return ret;
    }

}

class FunctionProofObligations {
    public String onlyIf;
    public String assumes;
    public String onSuccess;
    public List<String> assignable = new LinkedList<>();
    public boolean isGross;
}

class Environment {
    public Map<String,String> vars = new HashMap<>();
    public Map<String,String> cumulativeLogicalVars = new HashMap<>();
    public Map<String,Environment.FunctionInfo> funcs = new HashMap<>();

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
