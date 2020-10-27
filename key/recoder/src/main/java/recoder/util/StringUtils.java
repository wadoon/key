package recoder.util;

import java.io.File;
import java.util.StringTokenizer;

public class StringUtils {
    private static int tmpStrCount = 0;

    private static String[] tmpStrs = new String[64];

    private static void initTmpStrs() {
        for (int i = tmpStrs.length - 1; i >= 0; i--)
            tmpStrs[i] = null;
        tmpStrCount = 0;
    }

    private static void addTmpStr(String s) {
        if (tmpStrCount == tmpStrs.length) {
            int c = tmpStrCount;
            String[] newVal = new String[c * 2];
            System.arraycopy(tmpStrs, 0, newVal, 0, c);
            initTmpStrs();
            tmpStrs = newVal;
            tmpStrCount = c;
        }
        tmpStrs[tmpStrCount++] = s;
    }

    private static String[] getTmpStrVals() {
        String[] res = new String[tmpStrCount];
        System.arraycopy(tmpStrs, 0, res, 0, tmpStrCount);
        return res;
    }

    public static synchronized String[] split(String str, char separator) {
        if (str == null)
            return null;
        initTmpStrs();
        int start = 0;
        int idx = str.indexOf(separator, start);
        while (idx != -1) {
            String str1 = str.substring(start, idx);
            addTmpStr(str1);
            start = idx + 1;
            idx = str.indexOf(separator, start);
        }
        String hs = str.substring(start);
        addTmpStr(hs);
        return getTmpStrVals();
    }

    public static String basename(String s) {
        int lastIndex = s.lastIndexOf(File.separator);
        if (lastIndex == -1)
            return s;
        return s.substring(lastIndex + 1);
    }

    public static String basenameDot(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return s;
        return s.substring(lastIndex + 1);
    }

    public static String cutSuffix(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return s;
        return s.substring(0, lastIndex);
    }

    public static String cutPrefix(String s) {
        int firstIndex = s.indexOf('.');
        if (firstIndex == -1)
            return null;
        return s.substring(firstIndex + 1);
    }

    public static String removeDoubleQuotes(String s) {
        int firstIndex = s.indexOf("\"");
        int lastIndex = s.lastIndexOf("\"");
        if (lastIndex == -1 && firstIndex == -1)
            return s;
        if (lastIndex == firstIndex)
            return s;
        return s.substring(firstIndex + 1, lastIndex);
    }

    public static String getPrefix(String s) {
        int firstIndex = s.indexOf('.');
        if (firstIndex == -1)
            return null;
        return s.substring(0, firstIndex);
    }

    public static String getSuffix(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return null;
        return s.substring(lastIndex + 1);
    }

    public static String prependNameToSuffix(String prepend, String s) {
        String newBaseName, prefix = cutSuffix(s);
        String suffix = getSuffix(s);
        if (suffix == null) {
            newBaseName = prepend + s;
        } else {
            newBaseName = prefix + "." + prepend + suffix;
        }
        return newBaseName;
    }

    public static String stringReplace(String from, String pattern, String replacement) {
        int beginIndex = from.indexOf(pattern);
        String first = from.substring(0, beginIndex);
        first = first.concat(replacement);
        first = first.concat(from.substring(beginIndex + pattern.length()));
        return first;
    }

    public static String stringArray2String(String[] argv) {
        String returnString = "";
        for (int i = 0; i < argv.length; i++) {
            returnString = returnString + argv[i];
            if (i <= argv.length - 1)
                returnString = returnString + " ";
        }
        return returnString;
    }

    public static String[] string2StringArray(String s) {
        StringTokenizer tokenizer = new StringTokenizer(s, " ");
        int tokenCount = tokenizer.countTokens();
        String[] returnArray = new String[tokenCount + 1];
        if (tokenCount == 0)
            return returnArray;
        int i = 0;
        while (tokenizer.hasMoreTokens()) {
            returnArray[i] = tokenizer.nextToken(" ");
            i++;
        }
        return returnArray;
    }

    public static boolean parseBooleanProperty(String str) {
        if (str.equalsIgnoreCase("true"))
            return true;
        if (str.equalsIgnoreCase("false"))
            return false;
        if (str.equalsIgnoreCase("t"))
            return true;
        if (str.equalsIgnoreCase("f"))
            return false;
        if (str.equalsIgnoreCase("yes"))
            return true;
        if (str.equalsIgnoreCase("no"))
            return false;
        if (str.equals("1"))
            return true;
        if (str.equals("0"))
            return false;
        throw new IllegalArgumentException(str + " cannot be interpreted as boolean value");
    }
}
