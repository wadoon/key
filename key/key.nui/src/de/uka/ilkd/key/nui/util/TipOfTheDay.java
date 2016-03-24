package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.io.IOException;
import java.util.Random;

import org.key_project.util.java.IOUtil;

/**
 * Parses hints stored in {@link NUIConstants#TIPS_OF_THE_DAY_PATH}, collects
 * them in an array and makes them available randomly.
 * <p>
 * To add or remove tips edit the file at the above mentioned path. One line per
 * tip and make sure there is no empty lines.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 */
public final class TipOfTheDay {

    private final static Random r = new Random();
    private final static String[] TIPS = getTipsFromFile();

    /**
     * Randomly select a string out of the TIPS array.
     * 
     * @return randomly selected tip
     */
    public static String get() {
        return TIPS[r.nextInt(TIPS.length)];
    }

    /**
     * Reads strings from file and stores them in an array separated by a line
     * break.
     * 
     * @return Array of tips as strings separated by a line break
     */
    private static String[] getTipsFromFile() {
        try {
            String res = IOUtil.readFrom(new File(NUIConstants.TIPS_OF_THE_DAY_PATH));
            return res.split("\\R");
        }
        catch (IOException e) {
            return new String[] { "" };
        }
    }
}