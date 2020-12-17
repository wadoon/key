package org.key_project.cocos.maxintbuggy;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Random;

import org.key_project.sed.wrapper.ClassVerificationIter;
import org.key_project.sed.wrapper.SymbolicExecutionWrapper;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class PartSpecLearning {
    static int[][] arrs;
    
    public static void printarrs() {
        System.out.print("{\n");
        for (int i = 0; i < arrs.length; i++) {
            System.out.print("{");
            for (int k = 0; k < arrs[i].length; k++) {
                System.out.print(arrs[i][k]);
                System.out.print(", ");
            }
            System.out.print("},\n");
        }
        System.out.print("}\n");
    }
    
    /**
     * The program entry point.
     * @param args The start parameters.
     */
    public static void main(String[] args) {
        arrs = randompreconditions(100, 4);

        printarrs();
        
//        File location = new File("example"); // Path to the source code folder
//        String className = "MaxIntBuggy";
//        String methodName = "max";
//        String[] methodArgTypes = {}; //"int[]"};
//        String preconditionCustom = null;
//        try {
//            preconditionCustom
//                = new String(Files.readAllBytes( Paths.get("/home/lukas/key/git/key/key/keyext.extract_traces/precondition")));
//        } catch(Exception e) {}
//
//        SymbolicExecutionWrapper seWrapper = null;
//        String precondition;
//
//        try {
////            for (int i = 64; i <= 1024; i <<= 1) {
////                precondition = randompreconditions(i, 7);
////
////                final long timeStart = System.currentTimeMillis();
////                seWrapper = new SymbolicExecutionWrapper(location, className, methodName, methodArgTypes,
////                        precondition, null, null, null);
////                final long timeEnd = System.currentTimeMillis();
////
////                //System.out.println("Finished building SE tree");
////                //seWrapper.printSymbolicExecutionTree();
////                seWrapper.dispose();
////
////                System.out.println("" + i + " " + (timeEnd - timeStart)); 
////            }
//            seWrapper = new SymbolicExecutionWrapper(location, className, methodName, methodArgTypes,
//                  preconditionCustom, null, null, null);
//            System.out.println("Finished building SE tree");
//            seWrapper.printSymbolicExecutionTree(true);
//            seWrapper.dispose();
//        } catch (ProofInputException e) {
//            System.out.println("Exception at '" + location + "':");
//            e.printStackTrace();
//        } catch (ProblemLoaderException e) {
//            System.out.println("Exception at '" + location + "':");
//            e.printStackTrace();
//        }
//        System.exit(-1);
    }

    
    public static void mainClassVeri(String[] args) {
        boolean retval = true;
        ClassVerificationIter veriIter;
        try {
            System.out.println("Argument 0: " + args[0] + " Argument 1:" +  args[1]);
            veriIter = new ClassVerificationIter(new File(args[0]), args[1], null, null, null);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
            System.exit(-1);
            return; // dead code, needed by the java compiler
        }

        for (Boolean closed : veriIter) {
            retval = retval && closed;
        }
        if (retval) {
            System.exit(0);
        } else {
            System.exit(1);
        }
    }

    private static int[][] randompreconditions (int count, int maxArrLen) {
        Random rand = new Random();

        int[][] sb = new int[count][];
        for (int i = 0; i < count; i++) {
            int l = rand.nextInt(maxArrLen) + 1;
            sb[i] = new int [l];
            for (int k = 0; k < l; k++) {
                // r is between 0 and 100 (and not -100300003, just for convenience)
                int r = rand.nextInt(100);
                sb[i][k] = r;
            }
        }
        return sb;
    }

}
