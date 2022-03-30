package de.uka.ilkd.key.parser.solidity;

import de.uka.ilkd.key.parser.solidity.Solidity;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

public class SpecCompilerUtils {
    public static final String LIBRARY_TEMPLATE_FILE = "include/template_lib.key";
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

    public static String loadTemplate(Solidity.ContractType type) {
        String fileName = type == Solidity.ContractType.CONTRACT ?
            CONTRACT_TEMPLATE_FILE :
            (type == Solidity.ContractType.LIBRARY ?
                LIBRARY_TEMPLATE_FILE : 
                null);
        try {
            return Files.readString(Path.of(fileName));
        } catch (IOException e) {
            e.printStackTrace();
            return "error";
        }
    }

    public static String injectHeap(HeapType heap, String str) {
        return str.replaceAll(SpecCompilerUtils.HEAP_PLACEHOLDER_STRING,heap.toString());
    }
}