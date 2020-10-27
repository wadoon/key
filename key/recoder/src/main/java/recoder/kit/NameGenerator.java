package recoder.kit;

import recoder.abstraction.ArrayType;
import recoder.abstraction.Type;
import recoder.convenience.Naming;

public class NameGenerator {
    public static final int SHORT_STYLE = -1;

    public static final int DEFAULT_STYLE = 0;

    public static final int LONG_STYLE = 1;

    private int attempt;

    private String[] derivates;

    public NameGenerator(String base) {
        this(base, 0);
    }

    public NameGenerator(String base, int strategy) {
        this.attempt = 0;
        guessNames(base, strategy);
    }

    public NameGenerator(Type type) {
        this.attempt = 0;
        while (type instanceof ArrayType)
            type = ((ArrayType) type).getBaseType();
        if (type instanceof recoder.abstraction.PrimitiveType) {
            guessNames(type.getName(), -1);
        } else {
            guessNames(type.getName(), 0);
        }
    }

    private static String[] getLetters(String base) {
        char c = Character.toLowerCase(base.charAt(0));
        if (c < 'y')
            return new String[]{base, "" + (char) (c + 1), "" + (char) (c + 2)};
        if (c < 'z')
            return new String[]{base, "" + (char) (c + 1)};
        return new String[]{base};
    }

    private static String[] separateWords(String base) {
        int len = base.length();
        StringBuffer[] buf = new StringBuffer[len / 2];
        int w = 0;
        buf[w] = new StringBuffer();
        buf[w].append(base.charAt(0));
        for (int i = 1; i < len - 1; i++) {
            char c = base.charAt(i);
            if (Character.isUpperCase(c)) {
                char d = base.charAt(i - 1);
                char e = base.charAt(i + 1);
                if (Character.isLowerCase(e) || e == '_' || Character.isLowerCase(d)) {
                    w++;
                    buf[w] = new StringBuffer();
                    buf[w].append(c);
                    continue;
                }
            }
            buf[w].append(c);
            continue;
        }
        buf[w].append(base.charAt(len - 1));
        String[] res = new String[w + 1];
        for (int j = 0; j <= w; j++)
            res[j] = buf[j].toString();
        return res;
    }

    private static boolean isVowel(char c) {
        c = Character.toLowerCase(c);
        return (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y');
    }

    private static String removeVowels(String str) {
        int len = str.length();
        StringBuffer res = new StringBuffer(len);
        for (int i = 0; i < len; i++) {
            char c = str.charAt(i);
            if (!isVowel(c))
                res.append(c);
        }
        return res.toString();
    }

    private static String[] deriveShortCuts(int index, String[] words) {
        String base = words[index];
        int len = base.length();
        String[] res = new String[6];
        int w = 0;
        char c0 = base.charAt(0);
        if (Character.isUpperCase(c0)) {
            String s = base.toLowerCase();
            if (!Naming.isKeyword(s))
                res[w++] = s;
        }
        if (len > 3) {
            char c1 = base.charAt(1);
            if (!isVowel(c1)) {
                String s = base.substring(0, 2).toLowerCase();
                if (!Naming.isKeyword(s))
                    res[w++] = s;
            }
            if (!isVowel(c0)) {
                String bs = removeVowels(base);
                if (bs.length() == 2 || (bs.length() == 3 && len > 4)) {
                    String s = bs.toLowerCase();
                    if (!Naming.isKeyword(s))
                        res[w++] = s;
                }
            }
            if (len > 4) {
                char c2 = base.charAt(2);
                if (!isVowel(c2)) {
                    String s = base.substring(0, 3).toLowerCase();
                    if (!Naming.isKeyword(s))
                        res[w++] = s;
                }
            }
        }
        char lc0 = Character.toLowerCase(c0);
        if (len > 1 || Character.isUpperCase(c0)) {
            String s = "" + lc0;
            if (!Naming.isKeyword(s))
                res[w++] = s;
        }
        for (int i = 1; i < w; i++) {
            String x = res[i];
            int k = i - 1;
            int xlen = x.length();
            while (k >= 0 && res[k].length() > xlen) {
                res[k + 1] = res[k];
                k--;
            }
            if (k >= 0 && res[k].equals(x)) {
                k++;
                w--;
                i--;
                for (; k < len; k++)
                    res[k] = res[k + 1];
            } else {
                res[k + 1] = x;
            }
        }
        String[] result = new String[w];
        for (int j = 0; j < w; j++)
            result[j] = res[j];
        return result;
    }

    public String getNextCandidate() {
        String res;
        if (this.attempt < this.derivates.length) {
            res = this.derivates[this.attempt];
        } else {
            res = this.derivates[0] + (2 + this.attempt - this.derivates.length);
        }
        this.attempt++;
        return res;
    }

    private void guessNames(String base, int strategy) {
        String[] words = separateWords(base);
        int len = words.length;
        if (strategy == 0)
            strategy = (len >= 4) ? -1 : 1;
        String[][] shortCuts = new String[len][];
        for (int i = 0; i < len; i++)
            shortCuts[i] = deriveShortCuts(i, words);
        if (strategy == -1) {
            StringBuffer res = new StringBuffer(len);
            for (int j = 0; j < len; j++)
                res.append(shortCuts[j][0]);
            if (len == 1) {
                this.derivates = getLetters(res.toString());
            } else {
                this.derivates = new String[]{res.toString()};
            }
        } else {
            int c = 1;
            int j;
            for (j = 0; j < len; j++)
                c += (shortCuts[j]).length - 1;
            this.derivates = new String[c];
            c = 0;
            for (j = 0; j < len; j++) {
                for (int k = (shortCuts[j]).length - ((j == 0) ? 1 : 2); k >= 0; k--) {
                    StringBuffer buf = new StringBuffer();
                    int m;
                    for (m = 0; m < j; m++)
                        buf.append(shortCuts[m][0]);
                    buf.append(shortCuts[j][k]);
                    for (m = j + 1; m < len; m++)
                        buf.append(words[m]);
                    this.derivates[c++] = buf.toString();
                }
            }
        }
    }
}
