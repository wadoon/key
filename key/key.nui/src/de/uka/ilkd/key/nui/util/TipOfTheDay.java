package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.io.IOException;
import java.util.Random;

import org.key_project.util.java.IOUtil;

public final class TipOfTheDay {

    private final static Random r = new Random();
    private final static String[] TIPS = getTipsFromFile();

    /**
     * Randomly select a string
     */
    public static String get() {
        return TIPS[r.nextInt(TIPS.length)];
    }

    /**
     * Reads strings from file.
     * @return 
     */
    private static String[] getTipsFromFile() {
        try {
            String res = IOUtil.readFrom(new File(NUIConstants.TIPS_OF_THE_DAY_PATH));
            return res.split("\n");
        }
        catch (IOException e) {
            return new String[] { "" };
        }
    }
}