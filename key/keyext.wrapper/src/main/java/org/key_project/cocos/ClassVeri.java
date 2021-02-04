package org.key_project.cocos;

import java.io.File;

import org.key_project.cocos.wrapper.ClassVerificationIter;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class ClassVeri {
    public static void main(String[] args) {
        boolean retval = true;
        ClassVerificationIter veriIter;
        try {
            System.out.println("Argument 0: " + args[0] + " Argument 1:" +  args[1]);
            veriIter = new ClassVerificationIter(new File(args[0]), args[1], null, null, null);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
            printUsage();
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

    static void printUsage() {
        System.out.println("Usage:");
        System.out.println("ClassVeri <SOURCE_DIR> <CLASS_TO_VERIFY>");
    }
}
