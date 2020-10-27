package recoder.util;

import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

public abstract class CommandLineProgram {
    public static final Boolean TRUE = OptionManager.TRUE;

    public static final Boolean FALSE = OptionManager.FALSE;

    public static final Boolean ON = OptionManager.ON;

    public static final Boolean OFF = OptionManager.OFF;

    public static final int ONE = 1;

    public static final int ZERO_OR_ONE = 2;

    public static final int ONE_OR_MORE = 4;

    public static final int ZERO_OR_MORE = 8;

    public boolean showHelp;
    private final OptionManager om = new OptionManager();
    private final Map<String, Field> vars = new HashMap<String, Field>();

    protected abstract String getArgsDescription();

    protected abstract void run(String[] paramArrayOfString) throws Exception;

    protected void registerOptions() {
        registerSimpleOpt("showHelp", "h", "help", "display help information");
    }

    protected final void start(String[] args) {
        try {
            registerOptions();
            String[] remainingArgs = parseArgs(args);
            setVariables();
            if (this.showHelp)
                usage(true, 0);
            run(remainingArgs);
        } catch (OptionException oe) {
            handleOptionException(oe);
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }
    }

    protected void handleOptionException(OptionException oe) {
        try {
            setVariables();
        } catch (Exception e) {
        }
        if (this.showHelp) {
            usage(true, 0);
        } else {
            System.err.println(oe);
            usage(false, 1);
        }
    }

    protected final void registerSimpleOpt(String varName, String shortOpt, String longOpt, String descr) {
        registerSimpleOpt(varName, shortOpt, longOpt, descr, 2);
    }

    protected final void registerSimpleOpt(String varName, String shortOpt, String longOpt, String descr, int multiplicity) {
        registerVar(varName, shortOpt, Boolean.FALSE);
        this.om.addOption(0, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerSwitchOpt(String varName, String shortOpt, String longOpt, String descr, boolean defaultVal) {
        registerSwitchOpt(varName, shortOpt, longOpt, descr, 2, defaultVal);
    }

    protected final void registerSwitchOpt(String varName, String shortOpt, String longOpt, String descr, int multiplicity, boolean defaultVal) {
        registerVar(varName, shortOpt, new Boolean(defaultVal));
        this.om.addOption(1, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerBooleanOpt(String varName, String shortOpt, String longOpt, String descr, boolean defaultVal) {
        registerBooleanOpt(varName, shortOpt, longOpt, descr, 2, defaultVal);
    }

    protected final void registerBooleanOpt(String varName, String shortOpt, String longOpt, String descr, int multiplicity, boolean defaultVal) {
        registerVar(varName, shortOpt, new Boolean(defaultVal));
        this.om.addOption(2, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerNumberOpt(String varName, String shortOpt, String longOpt, String descr, int defaultVal) {
        registerNumberOpt(varName, shortOpt, longOpt, descr, 2, defaultVal);
    }

    protected final void registerNumberOpt(String varName, String shortOpt, String longOpt, String descr, int multiplicity, int defaultVal) {
        registerVar(varName, shortOpt, new Integer(defaultVal));
        this.om.addOption(3, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerStringOpt(String varName, String shortOpt, String longOpt, String descr, String defaultVal) {
        registerStringOpt(varName, shortOpt, longOpt, descr, 2, defaultVal);
    }

    protected final void registerStringOpt(String varName, String shortOpt, String longOpt, String descr, int multiplicity, String defaultVal) {
        registerVar(varName, shortOpt, defaultVal);
        this.om.addOption(4, multiplicity, shortOpt, longOpt, descr);
    }

    public void usage(boolean detailed, int exitcode) {
        this.om.showUsage("java " + getClass().getName(), getArgsDescription(), detailed);
        if (exitcode > -1)
            System.exit(exitcode);
    }

    private String[] parseArgs(String[] args) throws Exception {
        return this.om.parseArgs(args);
    }

    private void setVariables() throws Exception {
        for (String s : this.vars.keySet()) {
            Field f = this.vars.get(s);
            Object val = this.om.getValue(s);
            if (val != null)
                f.set(this, val);
        }
    }

    private void registerVar(String varName, String optStr, Object defVal) {
        try {
            Field var = getClass().getField(varName);
            var.set(this, defVal);
            this.vars.put(optStr, var);
        } catch (Exception e) {
            throw new RuntimeException("Internal error: " + e);
        }
    }
}
