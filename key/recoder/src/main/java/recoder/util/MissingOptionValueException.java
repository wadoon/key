package recoder.util;

public class MissingOptionValueException extends OptionException {
    private static final long serialVersionUID = -2394702516972821831L;

    public MissingOptionValueException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing value for option \"" + this.opt + "\"";
    }
}
