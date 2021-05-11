import java.util.*;
import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;

public class SpecCompilerUtils {
    public static final String LIBRARY_TEMPLATE_FILE = "include/template_interface.key";
    public static final String CONTRACT_TEMPLATE_FILE = "include/template_contract.key";

    public static final String HEAP_PLACEHOLDER_STRING = "__heap__";
    public static final String CONTRACT_NAME_PLACEHOLDER = "__contract_name_placeholder__";
    public static final String PROGRAM_VARIABLES_PLACEHOLDER = "__program_variables_placeholder__";
    public static final String SCHEMA_VARIABLES_PLACEHOLDER = "__schema_variables_placeholder__";
    public static final String INVARIANT_PLACEHOLDER = "__invariant_placeholder__";
    public static final String ASSUMPTION_PLACEHOLDER = "__assumption_placeholder__";
    public static final String FUNCTION_PLACEHOLDER = "__function_placeholder__";
    public static final String POSTCONDITION_PLACEHOLDER = "__postcondition_placeholder__";
    public static final String VARCOND_PLACEHOLDER = "__varcond_placeholder__";
    public static final String HEAP_UPDATE_PLACEHOLDER = "__heap_update_placeholder__";


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

    public static String loadTemplate() {
        try {
            return Files.readString(Path.of(CONTRACT_TEMPLATE_FILE));
        } catch (IOException e) {
            e.printStackTrace();
            return "error";
        }
    }

    public static String injectHeap(HeapType heap, String str) {
        return str.replaceAll(SpecCompilerUtils.HEAP_PLACEHOLDER_STRING,heap.toString());
    }

}
