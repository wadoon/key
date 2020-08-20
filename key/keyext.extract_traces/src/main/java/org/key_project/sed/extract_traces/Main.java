package org.key_project.sed.extract_traces;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Random;

import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.sed.wrapper.SymbolicExecutionWrapper;

/**
 * Example application which symbolically executes
 * {@code example/MaxIntBuggy}
 * Based on key.core.symbolic_execution.example
 * @author Lukas Grätz
 */
public class Main {
    /**
     * The program entry point.
     * @param args The start parameters.
     */
    public static void main(String[] args) {
        File location = new File("example"); // Path to the source code folder
        String className = "MaxIntBuggy";
        String methodName = "max";
        String[] methodArgTypes = {}; //"int[]"};
        String preconditionCustom = null;
        try {
            preconditionCustom
                = new String(Files.readAllBytes( Paths.get("/home/lukas/key/git/key/key/keyext.extract_traces/precondition")));
        } catch(Exception e) {}

        SymbolicExecutionWrapper seWrapper = null;
        String precondition;

        try {
//            for (int i = 64; i <= 1024; i <<= 1) {
//                precondition = randompreconditions(i, 7);
//
//                final long timeStart = System.currentTimeMillis();
//                seWrapper = new SymbolicExecutionWrapper(location, className, methodName, methodArgTypes,
//                        precondition, null, null, null);
//                final long timeEnd = System.currentTimeMillis();
//
//                //System.out.println("Finished building SE tree");
//                //seWrapper.printSymbolicExecutionTree();
//                seWrapper.dispose();
//
//                System.out.println("" + i + " " + (timeEnd - timeStart)); 
//            }
            seWrapper = new SymbolicExecutionWrapper(location, className, methodName, methodArgTypes,
                  preconditionCustom, null, null, null);
            System.out.println("Finished building SE tree");
            seWrapper.printSymbolicExecutionTree(true);
            seWrapper.dispose();
        } catch (ProofInputException e) {
            System.out.println("Exception at '" + location + "':");
            e.printStackTrace();
        } catch (ProblemLoaderException e) {
            System.out.println("Exception at '" + location + "':");
            e.printStackTrace();
        }
    }
    
    
    public static String preconditionOld
            = "(  (arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                     "&& arr[2] == 3   && arr[3] == 4)"
            + "|| (arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                     "&& arr[2] == 3   && arr[3] == 2)"
            + "|| (arr.length == 3 && arr[0] == 0   && arr[1] == 1   && arr[2] == 3)"
            + "|| (arr.length == 3 && arr[0] == 0   && arr[1] == 2   && arr[2] == 6)"
            + "|| (arr.length == 3 && arr[0] == 2   && arr[1] == 4   && arr[2] == 3)"
            + "|| (arr.length == 3 && arr[0] == 4   && arr[1] == 8   && arr[2] == 6)"
            + "|| (arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
            + "|| (arr.length == 3 && arr[0] == 4   && arr[1] == 3   && arr[2] == 2)"
            + "|| (arr.length == 3 && arr[0] == 550 && arr[1] == 4470&& arr[2] == 10)"
            + "|| (arr.length == 3 && arr[0] > arr[1] && arr[0] == arr[2]))"
            + "&& arr != null";

    public static String preconditionGhostVar
            =    "(tc1 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                             "&& arr[2] == 3   && arr[3] == 4)"
            + "&& (tc2 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                             "&& arr[2] == 3   && arr[3] == 2)"
            + "&& (tc3 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 1   && arr[2] == 3)"
            + "&& (tc4 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 2   && arr[2] == 6)"
            + "&& (tc5 ==> arr.length == 3 && arr[0] == 2   && arr[1] == 4   && arr[2] == 3)"
            + "&& (tc6 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 8   && arr[2] == 6)"
            + "&& (tc7 ==> arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
            + "&& (tc8 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 3   && arr[2] == 2)"
            + "&& (tc9 ==> arr.length == 3 && arr[0] == 550 && arr[1] == 4470&& arr[2] == 10)"
            + "&& (tc0 ==> arr.length == 3 && arr[0] > arr[1] && arr[0] == arr[2])"
            + "&& (tc1 || tc2 || tc3 || tc4 || tc5 || tc6 || tc7 || tc8 || tc9 || tc0)"
            + "&& arr != null";
    public static String preconditionGhostInt
            =    "(tc == 1 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                             "&& arr[2] == 3   && arr[3] == 4)"
            + "&& (tc == 2 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1 "
            +                             "&& arr[2] == 3   && arr[3] == 2)"
            + "&& (tc == 3 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 1   && arr[2] == 3)"
            + "&& (tc == 4 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 2   && arr[2] == 6)"
            + "&& (tc == 5 ==> arr.length == 3 && arr[0] == 2   && arr[1] == 4   && arr[2] == 3)"
            + "&& (tc == 6 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 8   && arr[2] == 6)"
            + "&& (tc == 7 ==> arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
            + "&& (tc == 8 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 3   && arr[2] == 2)"
            + "&& (tc == 9 ==> arr.length == 3 && arr[0] == 550 && arr[1] == 4470&& arr[2] == 10)"
            + "&& (tc == 0 ==> arr.length == 3 && arr[0] > arr[1] && arr[0] == arr[2])"
            + "&& 0 <= tc && tc <= 9 "
            + "&& arr != null";
    public static String preconditionQuantified
            = "( \\exists int tc; 0 <= tc && tc <= 9;"
            +    "(tc == 1 ==> "
            +        "arr.length == 4 && arr[0] == 2 && arr[1] == 1 && arr[2] == 3 && arr[3] == 4)"
            + "&& (tc == 2 ==> "
            +        "arr.length == 4 && arr[1] == 1 && arr[2] == 3 && arr[3] == 2)"
            + "&& (tc == 3 ==> "
            +        "arr.length == 3 && arr[0] == 0 && arr[1] == 1 && arr[2] == 3)"
            + "&& (tc == 4 ==> "
            +        "arr.length == 3 && arr[0] == 0 && arr[1] == 2 && arr[2] == 6)"
            + "&& (tc == 5 ==> "
            +        "arr.length == 3 && arr[0] == 2 && arr[1] == 4 && arr[2] == 3)"
            + "&& (tc == 6 ==> "
            +        "arr.length == 3 && arr[0] == 4 && arr[1] == 8 && arr[2] == 6)"
            + "&& (tc == 7 ==> "
            +        "arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
            + "&& (tc == 8 ==> "
            +        "arr.length == 3 && arr[0] == 4 && arr[1] == 3 && arr[2] == 2)"
            + "&& (tc == 9 ==> "
            +        "arr.length == 3 && arr[0] == 550 && arr[1] == 4470 && arr[2] == 10)"
            + "&& (tc == 0 ==> "
            +        "arr.length == 3 && arr[0] > arr[1] && arr[0] == arr[2])"
            + ") && arr != null";

    private static String randompreconditions (int count, int maxArrLen) {
        Random rand = new Random();

        StringBuilder sb = new StringBuilder();
        sb.append("(\n");
        for (int i = 0; i < count; i++) {
            sb.append("  tc == ").append(i).append(" ==> \n");
            int l = rand.nextInt(maxArrLen);
            sb.append(    "       arr.length == ").append(l).append("\n");
            for (int k = 0; k < l; k++) {
                // r is between 0 and 100 (and not -100300003, just for convenience)
                int r = rand.nextInt(100);
                sb.append("    && arr[").append(k).append("] == ").append(r).append("\n");
            }
            sb.append(") && (\n");
        }
        sb.append("  arr != null && 0 <= tc && tc < ").append(count);
        sb.append("\n)\n");
        return sb.toString();
    }
}
