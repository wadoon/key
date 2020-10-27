package recoder.util;

import java.io.PrintStream;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class OptionManager {
    public static final int SIMPLE = 0;

    public static final int SWITCH = 1;

    public static final int BOOL = 2;

    public static final int NUM = 3;

    public static final int STRING = 4;
    public static final Boolean TRUE = Boolean.TRUE;
    public static final Boolean FALSE = Boolean.FALSE;
    public static final Boolean ON = TRUE;
    public static final Boolean OFF = FALSE;
    public static final int ONE = 1;
    public static final int ZERO_OR_ONE = 2;
    public static final int ONE_OR_MORE = 4;
    public static final int ZERO_OR_MORE = 8;
    private static final String[] optVals = new String[]{"", "on|off", "true|false", "<n>", "<s>"};
    private static final int SINGLE = 3;

    private static final int MULTI = 12;

    private static final int MANDATORY = 5;
    private static final String empty = "                                     ";
    Vector options = new Vector();

    Map str2opt = new HashMap<Object, Object>();

    Vector mandatories = new Vector();

    public void addOption(int type, String shortOpt, String longOpt, String description) {
        addOption(type, 2, shortOpt, longOpt, description);
    }

    public void addOption(int type, int multiplicity, String shortOpt, String longOpt, String description) {
        Debug.assertBoolean((0 <= type && type <= 4), "Illegal option type");
        Debug.assertBoolean((1 <= multiplicity && multiplicity <= 8), "Illegal multiplicity specification");
        Debug.assertNonnull(shortOpt, "No short id specified");
        Debug.assertNonnull(longOpt, "No long id specified");
        Debug.assertNonnull(description, "No description specified");
        OptionDescription descr = new OptionDescription();
        descr.type = type;
        descr.multiplicity = multiplicity;
        descr.shortOpt = shortOpt;
        descr.longOpt = longOpt;
        descr.description = description;
        this.options.addElement(descr);
        this.str2opt.put("-" + shortOpt, descr);
        this.str2opt.put("--" + longOpt, descr);
        if ((multiplicity & 0x5) != 0)
            this.mandatories.addElement(descr);
    }

    int getOptionCount() {
        return this.options.size();
    }

    int parseArg(String[] args, int offset) throws UnknownOptionException, OptionMultiplicityException, IllegalOptionValueException, MissingOptionValueException {
        String opt = args[offset];
        OptionDescription descr = (OptionDescription) this.str2opt.get(opt);
        if (descr == null)
            throw new UnknownOptionException(args[offset]);
        if ((descr.multiplicity & 0x3) != 0 && descr.values.size() > 0)
            throw new OptionMultiplicityException(opt);
        offset++;
        String sval = null;
        if (descr.type != 0) {
            if (offset == args.length)
                throw new MissingOptionValueException(opt);
            sval = args[offset++];
        }
        Object optval = null;
        switch (descr.type) {
            case 0:
                optval = TRUE;
                break;
            case 1:
                if ("on".equals(sval)) {
                    optval = ON;
                    break;
                }
                if ("off".equals(sval)) {
                    optval = OFF;
                    break;
                }
                throw new IllegalOptionValueException(opt, sval);
            case 2:
                if ("true".equals(sval)) {
                    optval = TRUE;
                    break;
                }
                if ("false".equals(sval)) {
                    optval = FALSE;
                    break;
                }
                throw new IllegalOptionValueException(opt, sval);
            case 3:
                try {
                    optval = new Integer(sval);
                } catch (NumberFormatException nfe) {
                    throw new IllegalOptionValueException(opt, sval);
                }
                break;
            case 4:
                optval = sval;
                break;
        }
        Debug.assertNonnull(optval);
        descr.values.addElement(optval);
        return offset;
    }

    public String[] parseArgs(String[] args) throws UnknownOptionException, OptionMultiplicityException, IllegalOptionValueException, MissingOptionValueException, MissingArgumentException {
        int offset = 0;
        while (offset < args.length && args[offset].startsWith("-"))
            offset = parseArg(args, offset);
        for (Enumeration<OptionDescription> mand = this.mandatories.elements(); mand.hasMoreElements(); ) {
            OptionDescription descr = mand.nextElement();
            if (descr.values.size() == 0)
                throw new MissingArgumentException(descr.shortOpt);
        }
        String[] result = new String[args.length - offset];
        System.arraycopy(args, offset, result, 0, result.length);
        return result;
    }

    protected void printArg(PrintStream out, OptionDescription descr) {
        String baseinfo = ("-" + descr.shortOpt + " " + optVals[descr.type]).trim();
        String arginfo = "";
        switch (descr.multiplicity) {
            case 1:
                arginfo = " " + baseinfo;
                break;
            case 2:
                arginfo = " [" + baseinfo + "]";
                break;
            case 4:
                arginfo = " " + baseinfo + " [" + baseinfo + " ... " + baseinfo + "]";
                break;
            case 8:
                arginfo = " [" + baseinfo + " ... " + baseinfo + "]";
                break;
        }
        out.print(arginfo);
    }

    protected void printInfo(PrintStream out, OptionDescription descr, int sl, int ll, int vl) {
        String ss = (descr.shortOpt + "                                     ").substring(0, sl);
        String ls = (descr.longOpt + "                                     ").substring(0, ll);
        String vs = (optVals[descr.type] + "                                     ").substring(0, vl);
        out.println("  -" + ss + " " + vs + " | --" + ls + " " + vs + " : " + descr.description);
    }

    public void showUsage(PrintStream out, String programName, String params, boolean detailed) {
        out.print("usage: " + programName);
        int sl = 0;
        int ll = 0;
        int vl = 0;
        int i;
        for (i = 0; i < this.options.size(); i++) {
            OptionDescription descr = this.options.elementAt(i);
            sl = Math.max(sl, descr.shortOpt.length());
            ll = Math.max(ll, descr.longOpt.length());
            vl = Math.max(vl, optVals[descr.type].length());
            printArg(out, descr);
        }
        out.println(" " + params);
        if (detailed)
            for (i = 0; i < this.options.size(); i++)
                printInfo(out, this.options.elementAt(i), sl, ll, vl);
    }

    public void showUsage(String programName, String params, boolean detailed) {
        showUsage(System.out, programName, params, detailed);
    }

    public Vector getValues(String opt) {
        OptionDescription descr = (OptionDescription) this.str2opt.get("-" + opt);
        if (descr == null)
            return null;
        return descr.values;
    }

    public Object getValue(String opt) {
        Vector vals = getValues(opt);
        if (vals != null && vals.size() > 0)
            return vals.elementAt(0);
        return null;
    }

    public boolean isSet(String opt) {
        return (getValue(opt) == TRUE);
    }

    public boolean getBooleanVal(String opt) {
        return getBooleanVal(opt, false);
    }

    public boolean getBooleanVal(String opt, boolean defaultVal) {
        Object v = getValue(opt);
        if (v == null)
            return defaultVal;
        return (v == TRUE);
    }

    public int getIntVal(String opt) {
        return getIntVal(opt, 0);
    }

    public int getIntVal(String opt, int defaultVal) {
        Object v = getValue(opt);
        if (v == TRUE)
            return 1;
        if (v == FALSE)
            return 0;
        try {
            Integer i = (Integer) v;
            return i.intValue();
        } catch (Exception e) {
            return defaultVal;
        }
    }

    public String getStringVal(String opt) {
        return getStringVal(opt, null);
    }

    public String getStringVal(String opt, String defaultVal) {
        String result = (String) getValue(opt);
        if (result == null)
            return defaultVal;
        return result;
    }

    private class OptionDescription {
        int type;

        int multiplicity;

        String shortOpt;

        String longOpt;

        String description;
        Vector values = new Vector();

        private OptionDescription() {
        }
    }
}
